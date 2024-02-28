module Type = Rtype
module Translate = Rtranslate
module Infer = Rinfer
module Rhflz = Rhflz
module Result = Rresult
module Chc = Chc
module Remove_disjunctions = Remove_disjunctions

let rec generate_env = function 
  | [] -> Hflmc2_syntax.IdMap.empty
  | x::xs -> 
    let m = generate_env xs in
    let open Rhflz in
    Hflmc2_syntax.IdMap.add m x.var x.var.ty
  
let rec print_types = function
  | [] -> ()
  | x::xs -> 
    let open Rhflz in
    Rtype.print_rtype x.var.ty;
    print_newline ();
    print_types xs

let merge_rid_maps m1 m2 =
  Rid.M.merge
    (fun _id d1 d2 ->
      match d1, d2 with
      | Some d, None
      | None, Some d ->
        Some d
      | Some d1, Some d2 ->
        assert false
      | None, None -> assert false
    )
    m1 m2

let rec subst_arith env fml =
  let open Hflmc2_syntax in
  match fml with
  | Arith.Int i -> Arith.Int i
  | Var v -> begin
    match IdMap.find env v with
    | Some i -> Var i
    | None -> assert false
  end
  | Op (op, as') -> Op (op, List.map (subst_arith env) as')
(*  | Size ls -> Size (subst_lsexpr env ls)
and subst_lsexpr env fml =
  let open Hflmc2_syntax in
  match fml with
  | Arith.Nil -> Arith.Nil
  | LVar v -> begin
    match IdMap.find env v with
    | Some ({Id.name=_;ty=`List;id=_} as v') -> Arith.LVar v'
    | _ -> assert false
  end
  | Cons (hd, tl) -> Cons (subst_arith env hd, subst_lsexpr env tl)
*)
let rec subst_fml env fml =
  let open Hflmc2_syntax in
  match fml with
  | Formula.Bool b -> Formula.Bool b
  | Var  _ -> assert false
  | Or  fs -> Or  (List.map (subst_fml env) fs)
  | And fs -> And (List.map (subst_fml env) fs)
  | Pred (p, as', ls') ->
    Pred (p, List.map (subst_arith env) as', ls')

let generate_anno_env_ty (aty: Hflmc2_syntax.Type.abstraction_ty) (rty: Rtype.t) =
  let open Hflmc2_syntax in
  let rec go_ty env (aty: Hflmc2_syntax.Type.abstraction_ty) (rty: Rtype.t) = match aty, rty with
    | Type.TyBool fml, Rtype.RBool fml' -> begin
      let template =
        match fml' with
        | RTemplate t -> t
        | _ -> assert false in
      print_endline @@ "fmls: " ^ (List.map Formula.show fml |> String.concat " ");
      match fml with
      | [fml] -> begin
        let fml = subst_fml env fml in
        let (id, args, lsargs) = template in
        let template_args =
          List.map (fun t -> match t with Arith.Var v -> v | _ -> assert false) args in
        Rid.M.singleton id (fml, template_args)
      end
      | [] -> Rid.M.empty
      | _ -> assert false
    end
    | Type.TyArrow (argty, ty), Rtype.RArrow (argty', ty') ->
      (* 'annot ty arg Id.t * 'annot ty *)
      let arg_opt, m1 = go_argty env argty.ty argty' in
      let env =
        match arg_opt with
        | Some arg -> begin
          assert (IdMap.find env argty = None);
          IdMap.add env argty arg
        end
        | None -> env in
      let m2 = go_ty env ty ty' in
      merge_rid_maps
        m1
        m2
    | _ ->
      print_endline "ERROR: type mismatch (generate_anno_env_ty)";
      print_string "aty: ";
      print_endline @@ Type.show_abstraction_ty aty;
      print_string "rty: ";
      Rtype.print_rtype rty;
      assert false
  and go_argty env aty rty = match aty, rty with
    | Type.TyInt, Rtype.RInt rint -> begin
      match rint with
      | RId id ->
        (Some id), Rid.M.empty
      | RArith _ -> assert false
    end
    | Type.TySigma ty, (Rtype.RArrow _)
    | Type.TySigma ty, (Rtype.RBool _) ->
      None, go_ty env ty rty
    | _ -> assert false
  in
  go_ty IdMap.empty aty rty
      
  
let generate_anno_env (anno_env : Hflmc2_syntax.Type.abstraction_ty Hflmc2_syntax.IdMap.t) (env : Rtype.t Hflmc2_syntax.IdMap.t) =
  let open Hflmc2_syntax in
  let anno_env =
    IdMap.fold
      anno_env
      ~f:(fun ~key:id ~data:aty acc ->
        match IdMap.find env id with
        | Some rty ->
          merge_rid_maps
            acc
            (generate_anno_env_ty aty rty)
        | None ->
          print_endline @@ "NOT FOUND: " ^ Id.to_string id ^ " (maybe inlined)";
          acc
      )
      ~init:Rid.M.empty in
  anno_env

let main anno_env x top_old = 
  let y = Translate.translate x in
  let top_rule = Rhflz.lookup_rule top_old y in
  let top = top_rule.var in
  (*
  print_types y;
  print_newline();
  *)
  let env = generate_env y in
  let anno_env = generate_anno_env anno_env env in
  Infer.infer anno_env y env top