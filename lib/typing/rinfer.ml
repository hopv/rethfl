open Rhflz 
open Rtype
open Hflmc2_syntax
open Chc

type tractability = T_Tractable | T_Intractable
let tractability = ref T_Tractable
let show_tractability () =
  match !tractability with
  | T_Tractable -> "tractable"
  | T_Intractable -> "intractable"

(* timer*)
let measure_time f =
  let start  = Unix.gettimeofday () in
  let result = f () in
  let stop   = Unix.gettimeofday () in
  result, stop -. start
let times = let open Hflmc2_util in Hashtbl.create (module String)
let add_mesure_time tag f =
   let open Hflmc2_util in
  let r, time = measure_time f in
  let if_found t = Hashtbl.set times ~key:tag ~data:(t+.time) in
  let if_not_found _ = Hashtbl.set times ~key:tag ~data:time in
  Hashtbl.find_and_call times tag ~if_found ~if_not_found;
  r
let report_times () =
   let open Hflmc2_util in
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

(* The above code should be merged in hflmc2.ml... *)

let new_var () = RId(Id.gen `Int)
let new_lvar () = RLId(Id.gen `List)
let rec rty = function
  | RArrow(_, s) -> rty s
  | RBool(phi) -> phi
  | _ -> failwith "program error(rty)"

let add_constraint x m = 
  match x.head with
  | RTemplate(p, l, q) ->
  begin
    let rec find_template = function 
      | RTemplate(p', l', q') when p = p' && l = l' && q = q' -> true
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
   let t2 = subst x (RIntP(v)) t in
   let t2' = subst y (RIntP(v)) t' in
   _subtype t2 t2' renv m
 | RArrow(RList(RLId(x)), t), RArrow(RList(RLId(y)), t')  ->
   (* substitute generate new variable and substitute t and t' by the new var *)
   let v = new_lvar () in
   let t2 = subst x (RListP(v)) t in
   let t2' = subst y (RListP(v)) t' in
   _subtype t2 t2' renv m
 | RArrow(t, s), RArrow(t', s') ->
   let m' = 
   if !Hflmc2_options.Typing.mode_burn_et_al then
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
let rec infer_formula track formula env m ints lists = 
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
    let env' = IdMap.add env arg arg.ty in
    let (ints', lists') = 
      begin
      match arg.ty with
      | RInt (RId(i)) -> 
        (Arith.Var(i)::ints, lists)
      | RList (RLId(i)) -> 
        (ints, Arith.LVar(i)::lists)
      | _ -> (ints, lists) 
      end
    in
    let (body_t, l) = infer_formula track body env' m ints' lists' in
    (RArrow(arg.ty, body_t), l)
  | Forall(arg, body, template) ->
    let env' = IdMap.add env arg arg.ty in
    let (ints', lists') = 
      begin
      match arg.ty with
      | RInt (RId(i)) -> 
        (Arith.Var(i)::ints, lists)
      | RList (RLId(i)) -> 
        (ints, Arith.LVar(i)::lists)
      | _ -> (ints, lists) 
      end
    in
    let (body_t, l) = infer_formula track body env' m ints' lists' in
    let template = (RBool(RTemplate template)) in
    let l'' = subtype body_t template l in
    (template, l'')
  | Pred (f, args) -> (RBool(RPred(f, args)), m)
  | Arith x -> (RInt (RArith x), m)
  | Or (x, y, _, _) ->
    let (x', mx) = infer_formula track x env m ints lists in
    let (y', m') = infer_formula track y env mx ints lists in
    let (rx, ry) = match (x', y') with
      | (RBool(rx), RBool(ry)) -> (rx, ry)
      | _ -> failwith "type is not correct"
    in 
    RBool(ROr(rx, ry)), m'
  | LsArith x -> (RList (RLsArith x), m)
  | LsPred (f, args) -> (RBool(RLsPred(f, args)), m)
  | And (x, y, t1, t2) -> 
    let (x', mx) = infer_formula track x env m ints lists in
    let (y', m') = infer_formula track y env mx ints lists in
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
    let (x', mx) = infer_formula track x env m ints lists in
    let (y', m') = infer_formula track y env mx ints lists in
    let (arg, body, tau) = match (x', y') with
      | (RArrow(arg, body), tau) -> (arg, body, tau)
      | _ -> failwith "type is not correct"
    in begin
      match (arg, tau) with
       | RInt(RId(id)), RInt m -> 
         (subst id (RIntP(m)) body, m')
       | RList(RLId(id)), RList m -> 
         (subst id (RListP(m)) body, m')
       | _ ->
        let body' = clone_type_with_new_pred ints lists body in 
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
  let (t, m) = infer_formula track rule.body env chcs [] [] in
  let m = subtype t rule.var.ty m in
  print_string "[Result]\n";
  print_constraints m;
  m
 
let rec infer_hes ?(track=false) (hes: hes) env (accum: (refinement, refinement) chc list): (refinement, refinement) chc list = match hes with
  | [] -> accum
  | rule::xs -> 
    infer_rule track rule env accum |> infer_hes ~track:track xs env 

let pp_rule ppf rule =
  Fmt.pf ppf "@[%a : %a.@]"
    Hflmc2_syntax.Print.id rule.var
    (pp_rtype Print.Prec.zero) rule.var.ty

let pp_hes ppf hes =
  Fmt.pf ppf "@[%a@]"
    (Fmt.list ~sep:Format.pp_force_newline pp_rule) hes
  
let rec print_hes x =
  pp_hes Fmt.stdout x;
  Fmt.flush Fmt.stdout ();
  print_newline ()
  
let rec dnf_size = function
  | [] -> 0
  | x::xs -> 
    let x = ref2dnf x.head |> List.length in
    let y = dnf_size xs in
    if x > y then x else y

let simplify = normalize

let formula_to_refinement fml =
  let rec go fml = match fml with
    | Formula.Bool true -> RTrue
    | Bool false -> RFalse
    | Var _ -> assert false
    | Or fs ->
      let rec g = function
        | [x] -> go x
        | x::xs -> ROr (go x, g xs)
        | [] -> assert false
      in
      g fs
    | And fs ->
      let rec g = function
        | [x] -> go x
        | x::xs -> RAnd (go x, g xs)
        | [] -> assert false
      in
      g fs
    | Pred (p, as') ->
      RPred (p, as')
    | LsPred (p, as') ->
      RLsPred (p, as')
  in
  go fml
  
let print_derived_refinement_type is_dual_chc (anno_env : (('a, [ `Int ] Id.t, _) Formula.gen_t * [ `Int ] Id.t list) Rid.M.t) hes constraints = 
  let rec gen_name_type_map constraints m = match constraints with
    | [] -> m
    | (id, args, body)::xs -> 
      m |> Rid.M.add id (args, body) |> gen_name_type_map xs
  in
  let m =
    gen_name_type_map constraints Rid.M.empty
    |> Rid.M.map (fun (args, fml) -> args, if is_dual_chc then Rtype.dual fml else fml) in
  let m' =
    Rid.M.map
      (fun (fml, args) ->
        (args, formula_to_refinement fml)
      )
      anno_env
  in
  let m =
    Rid.M.merge
      (fun _i a b ->
        match a, b with
        | Some x, None | None, Some x -> Some x
        | Some a, Some _ -> Some a
        | None, None -> assert false
      )
      m
      m' in
  let rec subst_ids map t = 
    match map with 
    | [] -> t
    | (src, dst):: xs -> 
      t |> subst_refinement src (RIntP(RArith(dst))) |> subst_ids xs
  in
  let rec zip l r = match (l, r) with 
    | [], [] -> []
    | [], _ | _ , [] -> failwith "program error(print_derived_refinement_type)"
    | x::xs, y::ys -> (x, y)::zip xs ys
  in
  let rec translate_ty = function 
    | RArrow (x, y) -> RArrow(translate_ty x, translate_ty y)
    | RBool(RTemplate(p, l, _)) -> 
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

exception ExnTractable
exception ExnIntractable

let dual_environment env =
  Rid.M.map
    (fun (fml, args) ->
      let fml = Formula.mk_not fml in
      (fml, args)
    )
    env

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
let rec infer anno_env hes env top = 
  let hes = List.map (fun x -> 
    let open Rhflz in 
     {x with body=Rhflz.translate_if x.body}) hes 
  in
  let call_solver_with_timer anno_env hes solver = 
    add_mesure_time "CHC Solver" @@ fun () ->
    Chc_solver.check_sat anno_env hes solver
  in
  let check_feasibility anno_env chcs = 
    (* 1. generate constraints by using predicates for tracking cex *)
    let p = Chc_solver.get_unsat_proof anno_env chcs `Eldarica in
    let open Disprove in
    match disprove p hes env top with
    | `Invalid -> `Unsat
    | `Unknown -> `Unknown
  in 
  (* CHC Size is 1, then it is tractable *)
  (* size: intersection type size *)
  let rec try_intersection_type anno_env chcs is_tractable =
    (* 
      if sat then return Valid
      if unsat then returns check_feasibility
    *)
    if not is_tractable then (
      (if !Hflmc2_options.stop_if_intractable || !Hflmc2_options.remove_disjunctions_if_intractable then raise ExnIntractable);
      tractability := T_Intractable
    );
    if is_tractable then (
      (if !Hflmc2_options.stop_if_tractable then raise ExnTractable);
      tractability := T_Tractable
    );
    let solver = Chc_solver.selected_solver is_tractable in
    match call_solver_with_timer anno_env chcs solver with
    | `Unsat when !Hflmc2_options.Typing.no_disprove -> `Unknown
    | `Unsat when not is_tractable ->
      print_string "[Warning]Currently, we cannot disprove the validity when some definite clause has or-head\n";
      `Unknown
    | `Unsat -> check_feasibility anno_env chcs
    | `Sat(x) -> `Sat(x)
    | `Fail -> `Fail
    | `Unknown -> `Unknown
  and infer_main ?(size=1) hes env top = 
    (* 1. generate constraints *)
    print_hes hes;
    let top_pred = get_top @@ Hflmc2_syntax.Id.(top.ty) in
    let constraints = infer_hes hes env [{head=RTemplate(top_pred); body=RTrue}] in
    (*print_constraints constraints;*)
    (* 2. optimize CHC (ECHC) *)
    let constraints = List.map (fun chc -> 
      {chc with head=translate_if chc.head}
    ) constraints in

    let simplified = simplify constraints in
    let size = dnf_size simplified in
    Printf.printf "[Size] %d\n" size;

    
    if !Hflmc2_options.tractable_check_only then (
      if size = 1 then raise ExnTractable;
      let simplified_dual = List.map Chc.dual constraints |> simplify in
      let size_dual = dnf_size simplified_dual in
      if size_dual = 1 then raise ExnTractable;
      raise ExnIntractable
    );
    
    if !Hflmc2_options.solve_dual = "auto" then begin
      if size > 1 then begin
        let simplified_dual = List.map Chc.dual constraints |> simplify in
        let size_dual = dnf_size simplified_dual in
        Printf.printf "[Dual Size] %d\n" size_dual;
        let min_size = if size < size_dual then size else size_dual in
        let target = if size < size_dual then simplified else simplified_dual in
        let use_dual = size >= size_dual in
        let anno_env = if use_dual then dual_environment anno_env else anno_env in

        (* let target' = expand target in
        print_string "remove or or\n";
        print_constraints target'; *)
        (* 3. check satisfiability *)
        (*match call_solver_with_timer target' (Chc_solver.selected_solver 1) with
        | `Sat(x) -> `Sat(x)
        | `Fail -> failwith "hoge"
        | _ ->
          begin*)
        if min_size > 1 then begin
          (* if size > 1 /\ dual_size > 1 *)
          print_string "[Warning]Some definite clause has or-head\n";
          use_dual, try_intersection_type anno_env target false
        end else begin
          (* if dual_size <= 1 *)
          use_dual, try_intersection_type anno_env target true
        end
        (*end*)
      end else begin (* if size <= 1 *)
        false, try_intersection_type anno_env simplified true
      end
    end else if !Hflmc2_options.solve_dual = "auto-conservative" then begin
      if size > 1 then begin
        let simplified_dual = List.map Chc.dual constraints |> simplify in
        let size_dual = dnf_size simplified_dual in
        Printf.printf "[Dual Size] %d\n" size_dual;
        if size_dual <= 1 then
          (* if dual_size <= 1 *)
          true, try_intersection_type anno_env simplified_dual true
        else begin
          print_string "[Warning]Some definite clause has or-head\n";
          false, try_intersection_type anno_env simplified false
        end
      end else begin (* if size <= 1 *)
        false, try_intersection_type anno_env simplified true
      end
    end else if !Hflmc2_options.solve_dual = "dual" then begin
      print_endline "solve dual";
      let target = List.map Chc.dual constraints |> simplify in
      let size_dual = dnf_size target in
      Printf.printf "[Dual Size] %d\n" size_dual;
      let anno_env = dual_environment anno_env in
      if size_dual > 1 then begin
        print_string "[Warning]Some definite clause has or-head\n";
        true, try_intersection_type anno_env target false
      end else begin
        true, try_intersection_type anno_env target true
      end
    end else begin
      assert (!Hflmc2_options.solve_dual = "non-dual");
      print_endline "non-dual";
      if size > 1 then begin
        print_string "[Warning]Some definite clause has or-head\n";
        false, try_intersection_type anno_env simplified false
      end else begin
        false, try_intersection_type anno_env simplified true
      end
    end
  in 
  let is_dual_chc, x = infer_main hes env top in
  report_times ();
  match x with
  | `Sat(x) -> 
      begin 
        match x with 
        | Ok(x) -> 
          let open Hflmc2_options in
          let hes = print_derived_refinement_type is_dual_chc anno_env hes x in
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
