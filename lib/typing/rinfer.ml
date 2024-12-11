module Options = Rethfl_options
module P = Parser

open Rhflz
open Rtype
open Rethfl_syntax
open Chc

module Parser = P

(* timer*)
let measure_time f =
  let start  = Unix.gettimeofday () in
  let result = f () in
  let stop   = Unix.gettimeofday () in
  result, stop -. start
let times = let open Rethfl_util in Hashtbl.create (module String)
let add_mesure_time tag f =
   let open Rethfl_util in
  let r, time = measure_time f in
  let if_found t = Hashtbl.set times ~key:tag ~data:(t+.time) in
  let if_not_found _ = Hashtbl.set times ~key:tag ~data:time in
  Hashtbl.find_and_call times tag ~if_found ~if_not_found;
  r
let report_times () =
   let open Rethfl_util in
  let kvs = Hashtbl.to_alist times in
  match List.max_elt ~compare (List.map kvs ~f:(String.length<<<fst)) with
  | None -> Print.pr "no time records"
  | Some max_len ->
      Print.pr "Profiling:@.";
      List.iter kvs ~f:begin fun (k,v) ->
        let s =
          let pudding = String.(init (max_len - length k) ~f:(Fn.const ' ')) in
          "  " ^ k ^ ":" ^ pudding
        in Print.pr "%s %f sec@." s v
      end

(* The above code should be merged in rethfl.ml... *)

let new_var () = RId(Id.gen `Int)
let rec rty = function
  | RArrow(_, s) -> rty s
  | RBool(phi) -> phi
  | _ -> failwith "program error(rty)"

let add_constraint x m =
  match x.head with
  | RTemplate(p, l) ->
  begin
    let rec find_template = function
      | RTemplate(p', l') when p = p' && l = l' -> true
      | RAnd(x, y) -> find_template x || find_template y
      | _ -> false
    in
    if find_template x.body then m else x::m
  end
  | _ -> x::m

(* check whether t <= t' holds *)
let rec _subtype t t' renv m =
  match (t, t') with
 | RBool(p), RBool(p') ->
    add_constraint ({body=conjoin renv p'; head=p}) m
 | RArrow(RInt(RId(x)), t), RArrow(RInt(RId(y)), t')  ->
   (* substitute generate new variable and substitute t and t' by the new var *)
   let v = new_var () in
   let t2 = subst x v t in
   let t2' = subst y v t' in
   _subtype t2 t2' renv m
 | RArrow(t, s), RArrow(t', s') ->
   let m' =
   if !Rethfl_options.Typing.mode_burn_et_al then
     _subtype t' t renv m
   else
     _subtype t' t (conjoin renv (rty s')) m
   in
   _subtype s s' renv m'
 | _, _ ->
   print_rtype t;
   Printf.printf "=";
   print_rtype t';
   print_newline ();
   failwith "program error(subtype)"

let subtype t t' m = _subtype t t' RTrue m

(* track: tracking And/Forall to track counterexample *)
let rec infer_formula track formula env m ints =
  match formula with
  | Bool b when b -> (RBool(RTrue), m)
  | Bool _ -> (RBool(RFalse), m)
  | Var id ->
    begin
    match IdMap.find env id with
    | Some(t) -> (t, m)
    | None ->
    Printf.printf "not found: %s" id.name;
    failwith "no var(infer_formula)"
    end
  | Abs (arg, body) ->
    let env' = IdMap.set env arg arg.ty in
    let ints' =
      begin
      match arg.ty with
      | RInt (RId(i)) ->
        Arith.Var(i)::ints
      | _ -> ints
      end
    in
    let (body_t, l) = infer_formula track body env' m ints' in
    (RArrow(arg.ty, body_t), l)
  | Forall(arg, body, template) ->
    let env' = IdMap.set env arg arg.ty in
    let ints' =
      begin
      match arg.ty with
      | RInt (RId(i)) ->
        Arith.Var(i)::ints
      | _ -> ints
      end
    in
    let (body_t, l) = infer_formula track body env' m ints' in
    let template = (RBool(RTemplate template)) in
    let l'' = subtype body_t template l in
    (template, l'')
  | Pred (f, args) -> (RBool(RPred(f, args)), m)
  | Arith x -> (RInt (RArith x), m)
  | Or (x, y, _, _) ->
    let (x', mx) = infer_formula track x env m ints in
    let (y', m') = infer_formula track y env mx ints in
    let (rx, ry) = match (x', y') with
      | (RBool(rx), RBool(ry)) -> (rx, ry)
      | _ -> failwith "type is not correct"
    in
    RBool(ROr(rx, ry)), m'
  | And (x, y, t1, t2) ->
    let (x', mx) = infer_formula track x env m ints in
    let (y', m') = infer_formula track y env mx ints in
    let (rx, ry) = match (x', y') with
      | (RBool(rx), RBool(ry)) -> (rx, ry)
      | _ -> failwith "type is not correct"
    in
    if track then
      let tx = RBool(RTemplate(t1)) in
      let mx = subtype (RBool(rx)) tx m' in
      let ty = RBool(RTemplate(t2)) in
      let my = subtype (RBool(ry)) ty mx in
      RBool(RAnd(RTemplate(t1), RTemplate(t2))), my
    else
      RBool(RAnd(rx, ry)), m'
  | App(x, y, _) ->
    let (x', mx) = infer_formula track x env m ints in
    let (y', m') = infer_formula track y env mx ints in
    let (arg, body, tau) = match (x', y') with
      | (RArrow(arg, body), tau) -> (arg, body, tau)
      | _ -> failwith "type is not correct"
    in begin
      match (arg, tau) with
       | RInt(RId(id)), RInt m ->
         (subst id m body, m')
       | _ ->
        let body' = clone_type_with_new_pred ints body in
        (*
        print_string "subtyping...";
        print_rtype @@ RArrow(arg, body); print_string " =? "; print_rtype @@ RArrow(tau, body'); print_newline();
        *)
        let m'' = subtype (RArrow(arg, body)) (RArrow(tau, body')) m' in
        (body', m'')
      end

let infer_rule track (rule: hes_rule) env (chcs: (refinement, refinement) chc list): (refinement, refinement) chc list =
  print_newline();
  print_newline();
  print_string "infering new formula: ";
  Printf.printf "%s = " rule.var.name;
  print_formula rule.body;
  print_newline();
  (* infer type of rule.body using env *)
  let (t, m) = infer_formula track rule.body env chcs [] in
  (* generate constraint that inferred type `t` is subtype of var type *)
  let m = subtype t rule.var.ty m in
  print_string "[Result]\n";
  print_constraints m;
  m

let rec infer_hes ?(track=false) (hes: hes) env (accum_constraints: (refinement, refinement) chc list): (refinement, refinement) chc list = match hes with
  | [] -> accum_constraints
  | rule::xs ->
    infer_rule track rule env accum_constraints |> infer_hes ~track:track xs env

let rec print_hes = function
  | [] -> ()
  | hes_rule::xs ->
    print_string hes_rule.var.name;
    print_string " ";
    print_rtype hes_rule.var.ty;
    print_newline ();
    print_hes xs

let rec dnf_size = function
  | [] -> 0
  | x::xs ->
    let x = ref2dnf x.head |> List.length in
    let y = dnf_size xs in
    if x > y then x else y

let simplify = normalize

let print_derived_refinement_type is_dual_chc hes constraints =
  let rec gen_name_type_map constraints m = match constraints with
    | [] -> m
    | (id, args, body)::xs ->
      m |> Rid.M.add id (args, body) |> gen_name_type_map xs
  in
  let m =
    gen_name_type_map constraints Rid.M.empty
    |> Rid.M.map (fun (args, fml) -> args, if is_dual_chc then Rtype.dual fml else fml) in
   let rec subst_ids map t =
    match map with
    | [] -> t
    | (src, dst):: xs ->
      t |> subst_refinement src (RArith dst) |> subst_ids xs
  in
  let rec zip l r = match (l, r) with
    | [], [] -> []
    | [], _ | _ , [] -> failwith "program error(print_derived_refinement_type)"
    | x::xs, y::ys -> (x, y)::zip xs ys
  in
  let rec translate_ty = function
    | RArrow (x, y) -> RArrow(translate_ty x, translate_ty y)
    | RBool(RTemplate(p, l)) ->
      let (args, body) = Rid.M.find p m in
      let map = zip args l in
      let body' = subst_ids map body in
      RBool(body')
    | x -> x
  in
  let rec inner =
    let open Rhflz in
    function
    | [] -> []
    | rule::hes ->
      let rule = {rule with var={rule.var with ty=translate_ty rule.var.ty}} in
      rule :: inner hes
  in
  inner hes

(* Algorithm
Input: hes(simply typed) env top
Output: Valid/Invalid/Fail/Unknown

[inference]
1. generate constraints
2. optimize CHC (ECHC)
3. check satisfiability
if sat then return Valid
if unsat then returns check_feasibility

[check_feasibility]
1. generate constraints by using predicates for tracking cex
2. generate unsat_proof
3. evaluate HFL formula along the proof
4. if the input is evaluated to false then returns Invalid
5. otherwise; returns Unknown
*)
let infer hes env top =
  let hes = List.map (fun x ->
    let open Rhflz in
     {x with body=Rhflz.translate_if x.body}) hes
  in
  let call_solver_with_timer hes solver =
    add_mesure_time "CHC Solver" @@ fun () ->
    Chc_solver.check_sat hes solver
  in
  let check_feasibility chcs =
    (* 1. generate constraints by using predicates for tracking cex *)
    let p = Chc_solver.get_unsat_proof chcs `Eldarica in
    let open Disprove in
    match disprove p hes env top with
    | `Invalid -> `Unsat
    | `Unknown -> `Unknown
  in
  (* CHC Size is 1, then it is tractable *)
  (* size: intersection type size *)
  let rec try_intersection_type chcs size =
    (*
      if sat then return Valid
      if unsat then returns check_feasibility
    *)
    match call_solver_with_timer chcs (Chc_solver.selected_solver 1) with
    | `Unsat when !Rethfl_options.Typing.no_disprove -> `Unknown
    | `Unsat -> check_feasibility chcs
    | `Sat(x) -> `Sat(x)
    | `Fail -> `Fail
    | `Unknown -> `Unknown
  and infer_main ?(size=1) hes env top =
    (* 1. generate constraints *)
    print_hes hes;
    let top_pred = get_top @@ Rethfl_syntax.Id.(top.ty) in
    let constraints = infer_hes hes env [{head=RTemplate(top_pred); body=RTrue}] in
    (*print_constraints constraints;*)
    (* 2. optimize CHC (ECHC) *)
    let constraints = List.map (fun chc ->
      {chc with head=translate_if chc.head}
    ) constraints in

    let simplified = simplify constraints in
    let size = dnf_size simplified in
    Printf.printf "[Size] %d\n" size;

    if size > 1 then begin
      (* この辺使ってなさそう、size<=1っぽい *)
      let dual = List.map Chc.dual constraints in
      let simplified_dual = simplify dual in
      let size_dual = dnf_size simplified_dual in
      Printf.printf "[Dual Size] %d\n" size_dual;
      let min_size = if size < size_dual then size else size_dual in
      let target = if size < size_dual then simplified else simplified_dual in
      let use_dual = size >= size_dual in

      (* let target' = expand target in
      print_string "remove or or\n";
      print_constraints target'; *)
      (* 3. check satisfiability *)
      (* match call_solver_with_timer target' (Chc_solver.selected_solver 1) with
      | `Sat(x) -> `Sat(x)
      | `Fail -> failwith "hoge"
      | _ ->
        begin *)
          if min_size > 1 then (print_string "[Warning]Some definite clause has or-head\n";flush stdout)
          else (print_string "easy\n"; flush stdout);
          if min_size > 1 then
            (* if size > 1 /\ dual_size > 1 *)
            use_dual, call_solver_with_timer target Chc_solver.(`Fptprove)
          else
            use_dual, try_intersection_type target min_size
        (* end *)
    end else (* if size <= 1 *)
      false, try_intersection_type simplified size
  in
  let is_dual_chc, x = infer_main hes env top in
  report_times ();
  match x with
  | `Sat(x) ->
      begin
        match x with
        | Ok(x) ->
          let open Rethfl_options in
          let hes = print_derived_refinement_type is_dual_chc hes x in
          if !Typing.show_refinement then
            print_hes hes
          else
            ()
        | Error(s) -> Printf.printf "%s\n" s
      end;
      `Sat
  | `Unsat -> `Unsat
  | `Fail -> `Fail
  | `Unknown -> `Unknown


let print_refinements (constraints: (int * [> `Int ] Id.t list * refinement) list) =
  print_endline "[Refinements]";
  List.iter (fun (i, ids, ref) -> (
    Printf.printf "[constraint %d]\n%s\n" i ([%derive.show: [> `Int ] Id.t list] ids);
    (* List.iter (fun x -> Printf.printf "%s " (Id.show  x)) ids; *)
    print_refinement ref;
    print_newline ();
    ()
  )) constraints;
  print_endline "[Refinements end]"


let print_env (env: Rtype.t IdMap.t) =
  print_string "[print_env:start]\n";
  Rethfl_syntax.IdMap.iteri env ~f:(fun ~key:key ~data:data -> (
    Printf.printf "%s[ID=%d]: " key.name key.id;
    print_rtype data;
    print_newline ()
  ));
  print_string "[print_env:end]\n"

type annotation_config = {
  annotated_func: string;
  annotated_type: Rtype.t; [@opaque]
  dependencies_annotated_func: string list;
  dependencies_toplevel: string list;
}
[@@deriving show]


let rec string_of_rty_skeleton (rty: Rtype.t) =
    match rty with
    | RArrow(x, y) -> "RArrow("^ (string_of_rty_skeleton x)^", "^( string_of_rty_skeleton y)^")"
    | RBool(_) -> "RBool(RTrue)"
    | RInt(_) -> "RInt(RId Rethfl_syntax.Id.(gen ~name:\"x\" `Int))"


let dependent_funs f (hes : Rhflz.hes) =
  let fvs f =
    let { Rhflz.body; _ } = List.find (fun { Rhflz.var; _ } -> Id.eq f var) hes in
    Rhflz.fvs body
  in
  let rec aux checked rest =
    match IdSet.choose rest with
    | None -> checked
    | Some f ->
      let fvs = fvs f in
      let rest' = IdSet.remove (IdSet.diff fvs checked) f in
      let checked' = IdSet.add checked f in
      aux checked' rest'
  in
  aux IdSet.empty (fvs f)

let annotation_of file (hes : hes) =
  let top_funs = List.map (fun { var; _ } -> var) hes in
  let open Rethfl_util in
  let annotated_func,annotated_type =
    In_channel.with_file file
      ~f:(fun cin ->
          cin
          |> Lexing.from_channel
          |> Parser.annot Lexer.token)
  in
  let annotated_func' = List.find_exn top_funs ~f:(fun f -> f.name = annotated_func) in
  let dependencies_annotated_func =
    dependent_funs annotated_func' hes
    |> IdSet.elements
    |> List.map ~f:(fun f -> f.Id.name)
  in
  let dependencies_toplevel =
    top_funs
    |> List.filter_map ~f:(fun var -> if Id.eq var annotated_func' then None else Some var.name)
  in
  {
    annotated_func;
    annotated_type;
    dependencies_annotated_func;
    dependencies_toplevel
  }
(*
let annotation_of file hes =
  let r = annotation_of file hes  in
  Format.printf "annotation: %a@." pp_annotation_config r;
  r
*)

(* infer with annotations *)
let infer_based_on_annotations hes (env: Rtype.t IdMap.t) top file =
  let annotation = annotation_of file hes in

  print_env env;

  let env = Rethfl_syntax.IdMap.mapi env ~f:(fun ~key:id ~data:rty -> (
    if id.name = annotation.annotated_func
        then annotation.annotated_type
        else rty
  )) in

  print_env env;

  let hes = List.map (fun x ->
    let open Rhflz in
      {x with body=Rhflz.translate_if x.body}) hes
  in
  let hes = List.filter (fun x -> x.var.name <> annotation.annotated_func && List.exists (fun s -> s = x.var.name) annotation.dependencies_toplevel) hes in
  print_hes hes;
  let call_solver_with_timer hes solver =
    add_mesure_time "CHC Solver" @@ fun () ->
    Chc_solver.check_sat hes solver
  in
  let check_feasibility chcs =
    (* 1. generate constraints by using predicates for tracking cex *)
    let p = Chc_solver.get_unsat_proof chcs `Eldarica in
    let open Disprove in
    match disprove p hes env top with
    | `Invalid -> `Unsat
    | `Unknown -> `Unknown
  in
  (* CHC Size is 1, then it is tractable *)
  (* size: intersection type size *)
  let rec try_intersection_type chcs size =
    (*
      if sat then return Valid
      if unsat then returns check_feasibility
    *)
    match call_solver_with_timer chcs (Chc_solver.selected_solver 1) with
    | `Unsat when !Rethfl_options.Typing.no_disprove -> `Unknown
    | `Unsat -> check_feasibility chcs
    | `Sat(x) -> `Sat(x)
    | `Fail -> `Fail
    | `Unknown -> `Unknown
  and infer_main ?(size=1) hes env top =
    (* 1. generate constraints *)
    print_hes hes;
    let top_pred: Rtype.template = get_top @@ Rethfl_syntax.Id.(top.ty) in
    let constraints = infer_hes hes env [{head=RTemplate(top_pred); body=RTrue}] in
    (*print_constraints constraints;*)
    (* 2. optimize CHC (ECHC) *)
    let constraints = List.map (fun chc ->
      {chc with head=translate_if chc.head}
    ) constraints in

    let simplified = simplify constraints in
    let size = dnf_size simplified in
    Printf.printf "[Size] %d\n" size;

    if size > 1 then begin
      (* この辺使ってなさそう、size<=1っぽい *)
      let dual = List.map Chc.dual constraints in
      let simplified_dual = simplify dual in
      let size_dual = dnf_size simplified_dual in
      Printf.printf "[Dual Size] %d\n" size_dual;
      let min_size = if size < size_dual then size else size_dual in
      let target = if size < size_dual then simplified else simplified_dual in
      let use_dual = size >= size_dual in


      let target' = expand target in
      print_string "remove or or\n";
      print_constraints target';
      (* 3. check satisfiability *)
      (* match call_solver_with_timer target' (Chc_solver.selected_solver 1) with
      | `Sat(x) -> `Sat(x)
      | `Fail -> failwith "hoge"
      | _ ->
        begin *)
          if min_size > 1 then (print_string "[Warning]Some definite clause has or-head\n";flush stdout)
          else (print_string "easy\n"; flush stdout);
          if min_size > 1 then
            (* if size > 1 /\ dual_size > 1 *)
            use_dual, call_solver_with_timer target Chc_solver.(`Fptprove)
          else
            use_dual, try_intersection_type target min_size
        (* end *)
    end else (* if size <= 1 *)
      false, try_intersection_type simplified size
  in
  let (is_dual_chc, x) = infer_main hes env top in
  report_times ();
  match x with
  | `Sat(x) ->
      begin
        (* Note: --show-refinement つけないと実行されません *)
        match x with
        | Ok(x) ->
          (* print_refinements x; *)
          let open Rethfl_options in
          let hes = print_derived_refinement_type is_dual_chc hes x in
          if !Typing.show_refinement then
            print_hes hes
          else
            ()
        | Error(s) -> Printf.printf "%s\n" s
      end;
      `Sat
  | `Unsat -> `Unsat
  | `Fail -> `Fail
  | `Unknown -> `Unknown

let check_annotation hes env top file =
  let annotation = annotation_of file hes in

  (* let app = List.find (fun x -> x.var.name = "APP") hes in
  print_string (string_of_rty_skeleton app.var.ty);
  failwith "hoge"; *)

  (* specify type of SUM in env *)
  print_env env;

  let env = Rethfl_syntax.IdMap.mapi env ~f:(fun ~key:id ~data:rty -> (
    if id.name = annotation.annotated_func
        then annotation.annotated_type
        else rty
  )) in

  print_env env;
  (* END: specify type of SUM in env *)

  let top = (List.find (fun x -> x.var.name = annotation.annotated_func) hes).var in
  let hes = List.map (fun x ->
    let open Rhflz in
      {x with body=Rhflz.translate_if x.body}) hes
  in

  (* remove unrelated rules *)
  let hes = List.filter (fun x -> List.exists (fun s -> s = x.var.name) annotation.dependencies_annotated_func) hes in

  (* modify the expected type of SUM in hes *)
  let hes = List.map (fun x ->
    if x.var.name = annotation.annotated_func then (
      {x with var={x.var with ty=annotation.annotated_type}}
    ) else x
  ) hes in
  (* END: modify the expected type of SUM in hes *)
  let call_solver_with_timer hes solver =
    add_mesure_time "CHC Solver" @@ fun () ->
    Chc_solver.check_sat hes solver
  in
  let check_feasibility chcs =
    (* 1. generate constraints by using predicates for tracking cex *)
    let p = Chc_solver.get_unsat_proof chcs `Eldarica in
    let open Disprove in
    match disprove p hes env top with
    | `Invalid -> `Unsat
    | `Unknown -> `Unknown
  in
  (* CHC Size is 1, then it is tractable *)
  (* size: intersection type size *)
  let rec try_intersection_type chcs size =
    (*
      if sat then return Valid
      if unsat then returns check_feasibility
    *)
    match call_solver_with_timer chcs (Chc_solver.selected_solver 1) with
    | `Unsat when !Rethfl_options.Typing.no_disprove -> `Unknown
    | `Unsat -> check_feasibility chcs
    | `Sat(x) -> `Sat(x)
    | `Fail -> `Fail
    | `Unknown -> `Unknown
  and infer_main ?(size=1) hes env top =
    (* 1. generate constraints *)
    print_hes hes;
    let constraints = infer_hes hes env [] in
    (*print_constraints constraints;*)
    (* 2. optimize CHC (ECHC) *)
    let constraints = List.map (fun chc ->
      {chc with head=translate_if chc.head}
    ) constraints in

    let simplified = simplify constraints in
    let size = dnf_size simplified in
    Printf.printf "[Size] %d\n" size;

    if size > 1 then begin
      (* この辺使ってなさそう、size<=1っぽい *)
      let dual = List.map Chc.dual constraints in
      let simplified_dual = simplify dual in
      let size_dual = dnf_size simplified_dual in
      Printf.printf "[Dual Size] %d\n" size_dual;
      let min_size = if size < size_dual then size else size_dual in
      let target = if size < size_dual then simplified else simplified_dual in
      let use_dual = size >= size_dual in


      let target' = expand target in
      print_string "remove or or\n";
      print_constraints target';
      (* 3. check satisfiability *)
      (* match call_solver_with_timer target' (Chc_solver.selected_solver 1) with
      | `Sat(x) -> `Sat(x)
      | `Fail -> failwith "hoge"
      | _ ->
        begin *)
          if min_size > 1 then (print_string "[Warning]Some definite clause has or-head\n";flush stdout)
          else (print_string "easy\n"; flush stdout);
          if min_size > 1 then
            (* if size > 1 /\ dual_size > 1 *)
            use_dual, call_solver_with_timer target Chc_solver.(`Fptprove)
          else
            use_dual, try_intersection_type target min_size
        (* end *)
    end else (* if size <= 1 *)
      false, try_intersection_type simplified size
  in
  let (is_dual_chc, x) = infer_main hes env top in
  report_times ();
  match x with
  | `Sat(x) ->
      begin
        match x with
        | Ok(x) ->
          let open Rethfl_options in
          let hes = print_derived_refinement_type is_dual_chc hes x in
          if !Typing.show_refinement then
            print_hes hes
          else
            ()
        | Error(s) -> Printf.printf "%s\n" s
      end;
      `Sat
  | `Unsat -> `Unsat
  | `Fail -> `Fail
  | `Unknown -> `Unknown
