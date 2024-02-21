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

module StringMap = Map.Make (String)

let rec string_of_rty_skeleton (rty: Rtype.t) =
    match rty with
    | RArrow(x, y) -> "RArrow("^ (string_of_rty_skeleton x)^", "^( string_of_rty_skeleton y)^")"
    | RBool(_) -> "RBool(RTrue)"
    | RInt(_) -> "RInt(RId Rethfl_syntax.Id.(gen ~name:\"x\" `Int))"

let annotation: annotation_config =
  if Option.is_none (Sys.getenv_opt "ANNOTATION") then Obj.magic () else 
  let annotation_sum = 
    let var_n = Rethfl_syntax.Id.gen ~name:"n" `Int in
    let var_s = Rethfl_syntax.Id.gen ~name:"s" `Int in
    RArrow(RInt(RId var_n),
      RArrow(* wp *)(
        RArrow(* post *)(
          RInt(RId var_s),
          RBool(RPred(Formula.Le, [Arith.Var var_n; Arith.Var var_s]))
        ),
        RBool(RTrue)
      )
    )
  in

  let annotated_type_array_init =
    let var_i = Rethfl_syntax.Id.gen ~name:"i" `Int in
    let var_n = Rethfl_syntax.Id.gen ~name:"n" `Int in
    let var_i_input = Rethfl_syntax.Id.gen ~name:"i_input" `Int in
    let var_v_input = Rethfl_syntax.Id.gen ~name:"v_input" `Int in
    let var_i_output = Rethfl_syntax.Id.gen ~name:"i_output" `Int in
    let var_v_output = Rethfl_syntax.Id.gen ~name:"v_output" `Int in
    RArrow(RInt(RId var_i), RArrow(RInt (RId var_n), RArrow(
      (* a_input *)RArrow(RInt(RId var_i_input),
        (* wp of a_input *)RArrow(
          (* post of a_input *)RArrow(RInt(RId var_v_input), RBool(
            ROr(
              (* 0 <= i_a_input < i ==> *)ROr(
                RPred(Formula.Lt, [Arith.Var var_i_input; Arith.Int 0]),
                RPred(Formula.Le, [Arith.Var var_i; Arith.Var var_i_input])
              ),
              RPred(Formula.Eq, [Arith.Var var_v_input; Arith.Int 1])
            )
          )),
          RBool(RTrue)
        )
      ),
      (* wp *)RArrow(
        (* post *)RArrow(
          (* a_output *)RArrow(RInt(RId var_i_output),
            (* wp of a_output[i] *)RArrow(
              (* post of a_output[i] *)RArrow(RInt(RId var_v_output), RBool(
                ROr(
                  (* 0 <= i_a_input < i ==> *)ROr(
                    RPred(Formula.Lt, [Arith.Var var_i_output; Arith.Int 0]),
                    RPred(Formula.Le, [Arith.Var var_n; Arith.Var var_i_output])
                  ),
                  RPred(Formula.Eq, [Arith.Var var_v_output; Arith.Int 1])
                )
              )),
              (* pre of a_output[i] *)RBool(RTrue)
            )
          ),
          RBool(RTrue)
        ),
        (* pre *)RBool(RTrue)
      )
    )))
  in

  let annotation_array_init = {
    annotated_func = "INIT";
    annotated_type = annotated_type_array_init;
    dependencies_annotated_func = ["INIT"];
    dependencies_toplevel = ["MAIN_500"; "INIT"];
  }
  in

  let annotation_array_init_idnat = {
    annotated_func = "INIT";
    annotated_type = annotated_type_array_init;
    dependencies_toplevel = ["MAIN_630"; "IDNAT"];
    dependencies_annotated_func = ["INIT"; "IDNAT"];
  } in

  let rand (rs: refinement list): refinement =
    match rs with
    | [] -> failwith "program error(rand)"
    | x::xs -> List.fold_left (fun x y -> RAnd(x, y)) x xs
  in

  let ror (rs: refinement list): refinement =
    match rs with
    | [] -> failwith "program error(ror)"
    | x::xs -> List.fold_left (fun x y -> ROr(x, y)) x xs
  in

  let inrange lower mid upper =
    RAnd(
      RPred(Formula.Le, [lower; mid]),
      RPred(Formula.Le, [mid; upper])
    ) in

  let inrange_halfopen lower mid upper =
    RAnd(
      RPred(Formula.Le, [lower; mid]),
      RPred(Formula.Lt, [mid; upper])
    ) in
  
  let annotation_kmp_loopShift = {
    dependencies_toplevel = ["MAIN_1425"; "LOOPSHIFT"; "LOOP"; "MAKE_ARRAY"];
    dependencies_annotated_func = ["LOOPSHIFT"];
    annotated_func = "LOOPSHIFT";
    annotated_type =
      let var_plen = Rethfl_syntax.Id.gen ~name:"plen" `Int in
      let var_slen = Rethfl_syntax.Id.gen ~name:"slen" `Int in
      let var_i = Rethfl_syntax.Id.gen ~name:"i" `Int in
      let var_j = Rethfl_syntax.Id.gen ~name:"j" `Int in
      let var_pat_i = Rethfl_syntax.Id.gen ~name:"pat_i" `Int in
      let var_pat_v = Rethfl_syntax.Id.gen ~name:"pat_v" `Int in
      let var_ain_i = Rethfl_syntax.Id.gen ~name:"ain_i" `Int in
      let var_ain_v = Rethfl_syntax.Id.gen ~name:"ain_v" `Int in
      let var_aout_i = Rethfl_syntax.Id.gen ~name:"aout_i" `Int in
      let var_aout_v = Rethfl_syntax.Id.gen ~name:"aout_v" `Int in
      RArrow(
        RInt(RId var_plen),
        RArrow(
          RInt(RId var_slen),
          RArrow(
            (* [start] pat: (int -> ((int -> bool) -> bool)) *)RArrow(
              RInt(RId var_pat_i),
              RArrow(
                RArrow(
                  RInt(RId var_pat_v),
                  RBool(RTrue)
                ),
                RBool(inrange (Arith.Int 0) (Arith.Var var_pat_i) (Arith.Op (Arith.Sub,[Arith.Var var_plen; Arith.Int 1])))
              )
            )(* [end] pat *),
            RArrow(
              RInt(RId var_i),
              RArrow(
                RInt(RId var_j),
                RArrow(
                  (* [start] shiftArray1: (int -> ((int -> bool) -> bool))*)
                    RArrow(
                      RInt(RId var_ain_i),
                      RArrow(
                        RArrow(
                          RInt(RId var_ain_v),
                          RBool(inrange (Arith.Int (-1)) (Arith.Var var_ain_v) (Arith.Op (Arith.Sub,[Arith.Var var_ain_i; Arith.Int 1])))
                        ),
                        RBool(inrange (Arith.Int 0) (Arith.Var var_ain_i) (Arith.Op (Arith.Sub,[Arith.Var var_plen; Arith.Int 1])))
                      )
                    )
                  (* [end] shiftArray1*),
                  RArrow(
                    (* [start] k: ((int -> ((int -> bool) -> bool)) -> bool) *)
                      RArrow(
                        RArrow(
                          RInt(RId var_aout_i),
                          RArrow(
                            RArrow(
                              RInt(RId var_aout_v),
                              RBool(inrange (Arith.Int (-1)) (Arith.Var var_aout_v) (Arith.Op (Arith.Sub,[Arith.Var var_aout_i; Arith.Int 1])))
                            ),
                            RBool(inrange (Arith.Int 0) (Arith.Var var_aout_i) (Arith.Op (Arith.Sub,[Arith.Var var_plen; Arith.Int 1])))
                          )
                        ),
                        RBool(RTrue (* pre *))
                      )
                    (* [end] k *),
                    RBool(
                      (* pre = plen>0 /\ i inrange[-1,plen-2] /\ j inrange[i+1,plen] *)
                      rand [
                        RPred(Formula.Lt, [Arith.Int 0; Arith.Var var_plen]);
                        inrange (Arith.Int (-1)) (Arith.Var var_i) (Arith.Op (Arith.Sub, [Arith.Var var_plen; Arith.Int 2]));
                        inrange (Arith.Op (Arith.Add, [Arith.Var var_i; Arith.Int 1])) (Arith.Var var_j) (Arith.Var var_plen);
                      ]  
                    )
                  )
                )
              )
            )
          )
        )
      )
  } in


  let annotation_kmp_loop = {
    dependencies_toplevel = ["MAIN_1425"; "LOOPSHIFT"; "LOOP"; "MAKE_ARRAY"];
    dependencies_annotated_func = ["LOOP"];
    annotated_func = "LOOP";
    annotated_type =
      let var_plen = Rethfl_syntax.Id.gen ~name:"plen" `Int in
      let var_slen = Rethfl_syntax.Id.gen ~name:"slen" `Int in
      let var_s = Rethfl_syntax.Id.gen ~name:"s" `Int in
      let var_p = Rethfl_syntax.Id.gen ~name:"p" `Int in
      let var_pat_i = Rethfl_syntax.Id.gen ~name:"pat_i" `Int in
      let var_pat_v = Rethfl_syntax.Id.gen ~name:"pat_v" `Int in
      let var_str_i = Rethfl_syntax.Id.gen ~name:"str_i" `Int in
      let var_str_v = Rethfl_syntax.Id.gen ~name:"str_v" `Int in
      let var_ain_i = Rethfl_syntax.Id.gen ~name:"ain_i" `Int in
      let var_ain_v = Rethfl_syntax.Id.gen ~name:"ain_v" `Int in
      let var_res = Rethfl_syntax.Id.gen ~name:"res" `Int in
      RArrow(
        RInt(RId var_plen),
        RArrow(
          RInt(RId var_slen),
          RArrow(
            (* [start] pat: (int -> ((int -> bool) -> bool)) *)RArrow(
              RInt(RId var_pat_i),
              RArrow(
                RArrow(
                  RInt(RId var_pat_v),
                  RBool(RTrue)
                ),
                RBool(inrange (Arith.Int 0) (Arith.Var var_pat_i) (Arith.Op (Arith.Sub,[Arith.Var var_plen; Arith.Int 1])))
              )
            )(* [end] pat *),
            RArrow(
              (* [start] shiftArray3: (int -> ((int -> bool) -> bool))*)
                RArrow(
                  RInt(RId var_ain_i),
                  RArrow(
                    RArrow(
                      RInt(RId var_ain_v),
                      RBool(inrange (Arith.Int (-1)) (Arith.Var var_ain_v) (Arith.Op (Arith.Sub,[Arith.Var var_ain_i; Arith.Int 1])))
                    ),
                    RBool(inrange (Arith.Int 0) (Arith.Var var_ain_i) (Arith.Op (Arith.Sub,[Arith.Var var_plen; Arith.Int 1])))
                  )
                )
              (* [end] shiftArray3*),
              RArrow(
                (* [start] str: (int -> ((int -> bool) -> bool)) *)RArrow(
                  RInt(RId var_str_i),
                  RArrow(
                    RArrow(
                      RInt(RId var_str_v),
                      RBool(RTrue)
                    ),
                    RBool(inrange (Arith.Int 0) (Arith.Var var_str_i) (Arith.Op (Arith.Sub,[Arith.Var var_slen; Arith.Int 1])))
                  )
                )(* [end] str *),
                RArrow(
                  RInt(RId var_s),
                  RArrow(
                    RInt(RId var_p),
                    RArrow(
                      (* [start] k: (int -> bool) *)
                        RArrow(
                          RInt(RId var_res),
                          RBool(RTrue)
                        )
                      (* [end] k *),
                      RBool(
                        (* pre = plen>0 /\ slen>0 /\ s inrange[0,slen] /\ p inrange[0,plen] *)
                        rand [
                          RPred(Formula.Lt, [Arith.Int 0; Arith.Var var_plen]);
                          RPred(Formula.Lt, [Arith.Int 0; Arith.Var var_slen]);
                          inrange (Arith.Int 0) (Arith.Var var_p) (Arith.Var var_plen);
                          inrange (Arith.Int 0) (Arith.Var var_s) (Arith.Var var_slen);
                        ]  
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
  } in

  let annotation_fold_fun_list_fold_right = {
    dependencies_toplevel = ["MAIN_1078"; "FOLD_RIGHT"; "MAKE_LIST"];
    dependencies_annotated_func = ["FOLD_RIGHT"];
    annotated_func = "FOLD_RIGHT";
    annotated_type =
      let var_x1 = Rethfl_syntax.Id.gen ~name:"x1" `Int in
      let rty_nat_to_nat () =
        let var_x = Rethfl_syntax.Id.gen ~name:"x" `Int in
        let var_y = Rethfl_syntax.Id.gen ~name:"y" `Int in
        RArrow(
          RInt(RId var_x), 
          RArrow(
            RArrow(
              RInt(RId var_y),
              RBool(RPred(Formula.Le, [Arith.Int 0; Arith.Var var_y]))
            ),
            RBool(RPred(Formula.Le, [Arith.Int 0; Arith.Var var_x]))
          )
        ) in
      let var_xs_len = Rethfl_syntax.Id.gen ~name:"xs_len" `Int in
      RArrow(
        (* [start] f: (nat -> M nat) -> (nat -> M nat) -> nat -> M nat *)
        RArrow(
          rty_nat_to_nat (),
          RArrow(
            rty_nat_to_nat (),
            rty_nat_to_nat ()
          )
        ),
        (* [end] f: (nat -> M nat) -> (nat -> M nat) -> nat -> M nat *)
        RArrow(
          RInt(RId var_xs_len),
          RArrow(
            (* [start] xs_getvalue: int -> M (nat -> M nat) *)
            RArrow(
              RInt(RId var_x1),
              RArrow(
                RArrow(
                  rty_nat_to_nat (),
                  RBool(RTrue)
                ),
                RBool(RTrue)
              )
            ),
            (* [end] xs_getvalue: int -> M (nat -> M nat) *)
            RArrow(
              (* [start] init: nat -> M nat *)
              rty_nat_to_nat (),
              (* [end] init: nat -> M nat *)
              RArrow(
                (* [start] k_fold_right: (nat -> M nat) -> bool *)
                RArrow(
                  rty_nat_to_nat (),
                  RBool(RTrue)
                ),
                (* [end] k_fold_right: (nat -> M nat) -> bool *)
                RBool(RTrue)
              )
            )
          )
        )
      )

  } in

  let annotation_fold_fun_list_make_list = {
    dependencies_toplevel = ["MAIN_1078"; "FOLD_RIGHT"; "MAKE_LIST"];
    dependencies_annotated_func = ["MAKE_LIST"];
    annotated_func = "MAKE_LIST";
    annotated_type =
      let var_n = Rethfl_syntax.Id.gen ~name:"n" `Int in
      let var_len = Rethfl_syntax.Id.gen ~name:"len" `Int in
      let var_i = Rethfl_syntax.Id.gen ~name:"i" `Int in
      let rty_nat_to_nat () =
        let var_x = Rethfl_syntax.Id.gen ~name:"x" `Int in
        let var_y = Rethfl_syntax.Id.gen ~name:"y" `Int in
        RArrow(
          RInt(RId var_x), 
          RArrow(
            RArrow(
              RInt(RId var_y),
              RBool(RPred(Formula.Le, [Arith.Int 0; Arith.Var var_y]))
            ),
            RBool(RPred(Formula.Le, [Arith.Int 0; Arith.Var var_x]))
          )
        ) in
      RArrow(
        RInt(RId var_n),
        RArrow(
          (* [start] k:(int -> (i:int -> M (x:int -> y:M int[ensures y>=0][requires x>=0])[requires 0<=i<len]) -> bool)*)
          RArrow(
            RInt(RId var_len),
            RArrow(
              RArrow(
                RInt(RId var_i),
                (* [start] M (x:nat -> y:M nat)[requires 0<=i<n]*)
                RArrow(
                  RArrow(
                    rty_nat_to_nat (),
                    RBool(RTrue)
                  ),
                  RBool(inrange_halfopen (Arith.Int 0) (Arith.Var var_i) (Arith.Var var_n))
                )
                (* [end] M (x:nat -> y:M nat)[requires 0<=i<n]*)
              ),
              RBool(RPred(Formula.Eq, [Arith.Var var_len; Arith.Var var_n]))
            )
          ),
          (* [end] k:(int -> (i:int -> M (x:int -> y:M int[ensures y>=0][requires x>=0])[requires 0<=i<len]) -> bool)*)
          RBool(RPred(Formula.Le, [Arith.Int 1; Arith.Var var_n]))
        )
      )
  } in

  (* This type was discovered by inference of annotation_fold_fun_list_fold_right *)
  let annotation_fold_fun_list_make_list2 = {
    dependencies_toplevel = ["MAIN_1078"; "FOLD_RIGHT"; "MAKE_LIST"];
    dependencies_annotated_func = ["MAKE_LIST"];
    annotated_func = "MAKE_LIST";
    annotated_type =
      let var_n = Rethfl_syntax.Id.gen ~name:"n" `Int in
      let var_len = Rethfl_syntax.Id.gen ~name:"len" `Int in
      let var_i = Rethfl_syntax.Id.gen ~name:"i" `Int in
      let var_x = Rethfl_syntax.Id.gen ~name:"x" `Int in
      let var_y = Rethfl_syntax.Id.gen ~name:"y" `Int in
      RArrow(
        RInt(RId var_n),
        RArrow(
          RArrow(
            RInt(RId var_len),
            RArrow(
              RArrow(
                RInt(RId var_i),
                RArrow(
                  RArrow(
                    RArrow(
                      RInt(RId var_x), 
                      RArrow(
                        RArrow(
                          RInt(RId var_y),
                          RBool(
                            RAnd(
                            RPred(Formula.Le, [Arith.Int 1; Arith.Var var_n]),
                            ROr(
                              RPred(Formula.Le, [Arith.Var var_x; Arith.Int (-1)]),
                              RPred(Formula.Le, [Arith.Int 0; Arith.Var var_y])
                            )
                          ))
                        ),
                        RBool(RTrue)
                      )
                    ),
                    RBool(RPred(Formula.Le, [Arith.Int 1; Arith.Var var_n]))
                  ),
                  RBool(RTrue)
                )
              ),
              RBool(RTrue)
            )
          ),
          RBool(RTrue)
        )
      )
  } in


  (* This is minor change of _make_list2 and is more natural *)
  let annotation_fold_fun_list_make_list3 = {
    dependencies_toplevel = ["MAIN_1078"; "FOLD_RIGHT"; "MAKE_LIST"];
    dependencies_annotated_func = ["MAKE_LIST"];
    annotated_func = "MAKE_LIST";
    annotated_type =
      let var_n = Rethfl_syntax.Id.gen ~name:"n" `Int in
      let var_len = Rethfl_syntax.Id.gen ~name:"len" `Int in
      let var_i = Rethfl_syntax.Id.gen ~name:"i" `Int in
      let var_x = Rethfl_syntax.Id.gen ~name:"x" `Int in
      let var_y = Rethfl_syntax.Id.gen ~name:"y" `Int in
      RArrow(
        RInt(RId var_n),
        RArrow(
          RArrow(
            RInt(RId var_len),
            RArrow(
              RArrow(
                RInt(RId var_i),
                RArrow(
                  RArrow(
                    RArrow(
                      RInt(RId var_x), 
                      RArrow(
                        RArrow(
                          RInt(RId var_y),
                          RBool(
                            RPred(Formula.Le, [Arith.Int 0; Arith.Var var_y])
                          )
                        ),
                        RBool(RPred(Formula.Le, [Arith.Int 0; Arith.Var var_x]))
                      )
                    ),
                    RBool(RPred(Formula.Le, [Arith.Int 1; Arith.Var var_n]))
                  ),
                  RBool(RTrue)
                )
              ),
              RBool(RTrue)
            )
          ),
          RBool(RTrue)
        )
      )
  } in

  let annotation_risers_risers = {
    dependencies_toplevel = ["MAIN_2208"; "RISERS"; "MAKE_LIST"];
    dependencies_annotated_func = ["RISERS"];
    annotated_func = "RISERS";
    annotated_type =
        let var_l1_len = Rethfl_syntax.Id.gen ~name:"l1_len" `Int in
        let var_l2_len = Rethfl_syntax.Id.gen ~name:"l2_len" `Int in
        RArrow(
          RInt(RId var_l1_len),
          RArrow(
            (* [start] l1_getvalue:(int -> (int -> bool) -> bool)*)
            RArrow(
              RInt(RId (Rethfl_syntax.Id.gen ~name:"x" `Int)),
              RArrow(
                RArrow(
                  RInt(RId (Rethfl_syntax.Id.gen ~name:"x" `Int)),
                  RBool(RTrue)
                ),
                RBool(RTrue)
              )
            ),
            (* [end] l1_getvalue:(int -> (int -> bool) -> bool)*)

            RArrow(
              (* [start] k *)
              RArrow(
                RInt(RId var_l2_len),
                RArrow(
                  (* [start] l2_getvalue *)
                  RArrow(
                    RInt(RId(Rethfl_syntax.Id.gen ~name:"i2" `Int)),
                    RArrow(
                      (* [start] k_v2:(v2_len:int -> v2_getvalue:(bool -> (int -> bool) -> bool) -> bool) *)
                      RArrow(
                        RInt(RId(Rethfl_syntax.Id.gen ~name:"v2_len" `Int)),
                        RArrow(
                          (* [start] v2_getvalue: (bool -> (int -> bool) -> bool) *)
                          RArrow(
                            RBool(RTrue),
                            RArrow(
                              RArrow(
                                RInt(RId(Rethfl_syntax.Id.gen ~name:"x" `Int)),
                                RBool(RTrue)
                              ),
                              RBool(RTrue)
                            )
                          ),
                          (* [end] v2_getvalue: (bool -> (int -> bool) -> bool) *)
                          RBool(RTrue)
                        )
                      ),
                      (* [end] k_v2:(v2_len:int -> v2_getvalue:(bool -> (int -> bool) -> bool) -> bool) *)
                      RBool(RTrue)
                    )
                  ),
                  (* [end] l2_getvalue *)
                  RBool((RAnd(
                    ROr(
                      RPred(Formula.Lt, [Arith.Int 0; Arith.Var var_l1_len]),
                      RPred(Formula.Le, [Arith.Var var_l2_len; Arith.Int 0])
                    ),
                    ROr(
                      RPred(Formula.Le, [Arith.Var var_l1_len; Arith.Int 0]),
                      RPred(Formula.Lt, [Arith.Int 0; Arith.Var var_l2_len])
                    )
                  )))
                )
              ),
              (* [end] k *)
              RBool(RTrue)
            )
          )
        )
  } in

  let annotation_risers_make_list = {
    dependencies_toplevel = ["MAIN_2208"; "RISERS"; "MAKE_LIST"];
    dependencies_annotated_func = ["MAKE_LIST"];
    annotated_func = "MAKE_LIST";
    annotated_type =
        RArrow(
          RInt(RId(Rethfl_syntax.Id.gen ~name:"m" `Int)),
          RArrow(
            RArrow(
              RInt(RId(Rethfl_syntax.Id.gen ~name:"len" `Int)),
              RArrow(
                RArrow(
                  RInt(RId (Rethfl_syntax.Id.gen ~name:"i" `Int)),
                  RArrow(
                    RArrow(
                      RInt(RId(Rethfl_syntax.Id.gen ~name:"v" `Int)),
                      RBool(RTrue)
                    ),
                    RBool(RTrue)
                  )
                ),
                RBool(RTrue)
              )
            ),
            RBool(RTrue)
          )
        )
  } in

  let annotation_indirectintro9_f = {
    dependencies_toplevel = ["MAIN_1524"; "F_WITHOUT_CHECKING_252"];
    dependencies_annotated_func = ["F_WITHOUT_CHECKING_252"; "APP"];
    annotated_func = "F_WITHOUT_CHECKING_252";
    annotated_type =
      let var_sff = Rethfl_syntax.Id.gen ~name:"sff" `Int in
      RArrow(
        RInt(RId Rethfl_syntax.Id.(gen ~name:"x" `Int)),
        RArrow(
          RInt(RId Rethfl_syntax.Id.(gen ~name:"x" `Int)),
          RArrow(
            RInt(RId Rethfl_syntax.Id.(gen ~name:"x" `Int)),
            RArrow(
              (* [start] k:((int -> int -> bool -> (bool -> bool) -> bool) -> bool) *)
              RArrow(
                RArrow(
                  RInt(RId var_sff),
                  RArrow(
                    RInt(RId Rethfl_syntax.Id.(gen ~name:"x" `Int)),
                    RArrow(
                      RBool(RFalse),
                      RArrow(
                        (* [start] bool -> bool *)
                        RArrow(
                          RBool(RFalse),
                          RBool(RTrue)
                        ),
                        (* [end] bool -> bool *)
                        RBool(RPred(Formula.Eq, [Arith.Int 0; Arith.Var var_sff]))
                      )
                    )
                  )
                ),
                RBool(RTrue)
              ),
              (* [end] k:((int -> int -> bool -> (bool -> bool) -> bool) -> bool) *)
              RBool(RTrue)
            )
          )
        )
      )
  } in

  let annotation_indirectintro9_app = {
    dependencies_toplevel = ["MAIN_1524"; "F_WITHOUT_CHECKING_252"; "APP"];
    dependencies_annotated_func = ["APP"];
    annotated_func = "APP";
    annotated_type =
        let intid () = RInt(RId (Rethfl_syntax.Id.gen ~name:"x" `Int)) in
        let rty_fin () = 
          let var_sff = Rethfl_syntax.Id.gen ~name:"sff" `Int in

                RArrow(
                  RInt(RId var_sff),
                  RArrow(
                    intid (),
                    RArrow(
                      RBool(RFalse),
                      RArrow(
                        (* [start] bool -> bool *)
                        RArrow(
                          RBool(RFalse),
                          RBool(RTrue)
                        ),
                        (* [end] bool -> bool *)
                        RBool(RPred(Formula.Eq, [Arith.Int 0; Arith.Var var_sff]))
                      )
                    )
                  )
                ) in
                let var_psff = Rethfl_syntax.Id.gen ~name:"psff" `Int in
                let var_sff2 = Rethfl_syntax.Id.gen ~name:"sff2" `Int in
    RArrow(intid (), RArrow(intid (), RArrow(intid (), RArrow(intid (), RArrow(intid (), RArrow(intid (), RArrow(intid (), RArrow(intid (),
    RArrow(
        (* [start] h*)
        RArrow(RInt(RId var_psff), RArrow(intid (), RArrow(intid (), RArrow(RArrow(
        (RArrow(
          RInt(RId var_sff2),
          RArrow(
            intid (),
            RArrow(
              RBool(RFalse),
              RArrow(
                (* [start] bool -> bool *)
                RArrow(
                  RBool(RFalse),
                  RBool(RTrue)
                ),
                (* [end] bool -> bool *)
                RBool(RPred(Formula.Eq, [Arith.Int 0; Arith.Var var_sff2]))
              )
            )
          )
        ))
        , RBool(RTrue)), RBool(RPred(Formula.Eq, [Arith.Int 0; Arith.Var var_psff])))))),
        (*[end] h*)
        RArrow(intid (), RArrow(intid (), RArrow(intid (), rty_fin ())))
        )
    ))))))))
  } in 

  let annotations = StringMap.of_seq @@ List.to_seq [
    (* ("SUM", annotation_sum); *)
    ("array_init", annotation_array_init);
    ("array_init_idnat", annotation_array_init_idnat);
    ("kmp_loopShift", annotation_kmp_loopShift);
    ("kmp_loop", annotation_kmp_loop);
    ("fun_fold_list_fold_right", annotation_fold_fun_list_fold_right);
    ("fun_fold_list_make_list", annotation_fold_fun_list_make_list); (* CHECK_TARGET=toplevel is untypable. why? *)
    ("fun_fold_list_make_list2", annotation_fold_fun_list_make_list2);
    ("fun_fold_list_make_list3", annotation_fold_fun_list_make_list3);
    ("risers_risers", annotation_risers_risers);
    ("risers_make_list", annotation_risers_make_list);
    ("indirectintro9_f", annotation_indirectintro9_f);
    ("indirectintro9_app", annotation_indirectintro9_app);
  ] in

  StringMap.find (Sys.getenv "ANNOTATION") annotations

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
  
  
