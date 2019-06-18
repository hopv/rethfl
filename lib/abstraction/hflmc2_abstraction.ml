open Hflmc2_util
open Hflmc2_syntax
open Type
module Fpat = FpatInterface

type env = abstraction_ty IdMap.t

(* For Or and And: (λxs.u1, λxs.u2) -> λxs.f u1 u2 *)
let merge_lambda : int -> (Hfl.t -> Hfl.t -> Hfl.t) -> Hfl.t -> Hfl.t -> Hfl.t =
  (*{{{*)
  fun len merge t1 t2 ->
    let new_vars = List.init len ~f:(fun _ -> Id.gen ATyBool) in

    let rec gather_vars len t = match t with
      | _ when len = 0 ->
          ([], t)
      | Hfl.Abs(x, t) ->
          let (xs, u) = gather_vars (len-1) t in
          (x::xs, u)
      | _ ->
          let x = Id.gen ATyBool in
          let (xs, u) = gather_vars (len-1) (Hfl.App(t, Var(x))) in
          (x::xs, u)
    in

    let rename orig_vars t =
      let map =
        try IdMap.of_alist_exn @@ List.zip_exn
              (List.map ~f:Id.remove_ty orig_vars)
              (List.map ~f:Hfl.mk_var new_vars)
        with
          | Invalid_argument _ -> assert false
          | _ -> assert false
      in
      Subst.Hfl.hfl map t
    in

    let u1' = Fn.uncurry rename @@ gather_vars len t1 in
    let u2' = Fn.uncurry rename @@ gather_vars len t2 in
    Hfl.mk_abss new_vars (merge u1' u2')
(*}}}*)

(* Γ |- σ <= σ ↪ φ' で得たφ'にφを適用 *)
let rec abstract_coerce : env -> abstraction_ty -> abstraction_ty -> Hfl.t -> Hfl.t =
  fun env sigma sigma' phi ->
    let debug = false in
    if false then begin
      Format_.pr "==================@.";
      Format_.print ~tag:"σ " Format_.abstraction_ty sigma;
      Format_.print ~tag:"σ'" Format_.abstraction_ty sigma';
    end;
    match sigma, sigma' with
    | TyBool ps, TyBool qs ->
        (* x[j] is a variable for q[j] *)
        let xs = List.init (List.length qs) ~f:(fun _ -> Id.gen ATyBool) in
        begin
        try
          (* Simple case: forall p[i], there exists j_i s.t. p[i] = q[j_i] *)
          let qxs = List.zip_exn qs xs in
          (* gather x[j_i] *)
          let pxs = List.map ps ~f:begin fun p ->
              snd @@ List.find_exn qxs ~f:(fun (q,_) -> Fpat.(p <=> q))
            end
          in
          (* assemble *)
          let phi' = Hfl.mk_abss xs @@ Hfl.mk_apps phi (List.map ~f:Hfl.mk_var pxs) in
          phi'
        with Not_found ->
          if debug then begin
            Format_.pr "==================@.";
            Format_.print ~tag:"xs" (Format_.list_comma Format_.id) xs;
            Format_.print ~tag:"φ " Format_.hfl phi;
          end;
          (* Let ps be P1,...,Pk and qs be Q1,...,Ql.
           * To compute φ, find I ⊆ {1,...,l} and J1,...,Jm ⊆ {1,...,k} such that
           *    [1] ∧ _{i \in I}Qi => ∨ _{h \in 1,...,m}∧ _{j \in Jh} Pj
           * Let
           *    [2] φ'_{I,J1,...,Jm} = ∧ _{i \in I}b_i ∧ _{h \in 1,...,m} φ (1 \in Jh) ... (l \in Jh)
           * then φ' is the union of all φ'_{I,J1,...,Jm}.
           * *)
          (* TODO Pjは束としてみたときの極大元のみ考える
           *      P1 = {1} と P2 = {1,2} を同時に考えてはいけない（式のサイズがヤバいことになる）
           *)
          let l = List.length qs in
          let k = List.length ps in
          let max_ors = 3 in (* TODO オプションで変えられるように *)

          let one_to_l = List.(range ?start:(Some `inclusive) ?stop:(Some `exclusive) 0 l) in
          let one_to_k = List.(range ?start:(Some `inclusive) ?stop:(Some `exclusive) 0 k) in
          let _Is = List.powerset one_to_l in
          let _Js =
              List.filter (List.powerset one_to_k) ~f:begin fun _J ->
                let ps' = List.(map ~f:(nth_exn ps) _J) in
                Fpat.is_consistent_set ps' && not (List.is_empty _J)
              end
          in
          let _Jss = List.filter (List.powerset ~limit:max_ors _Js)
              ~f:(fun l -> not (List.is_empty l)) in
          let phi's = List.map _Is ~f:begin fun _I ->
              let xs' = List.(map ~f:(nth_exn xs) _I) in
              let qs' = List.(map ~f:(nth_exn qs) _I) in
              let _Q  = Formula.mk_ands qs' in
              if Fpat.is_consistent_set qs' then begin
                let candidates : (int list list * Formula.t) list =
                  List.filter_map _Jss ~f:begin fun _Js ->
                    let pss =
                          List.map _Js ~f:begin fun _J ->
                            List.map _J ~f:begin fun j ->
                              List.nth_exn ps j end end
                    in
                    let body =
                          Formula.mk_ors @@ List.map ~f:Formula.mk_ands pss
                    in
                    if Fpat.(_Q ==> body)
                    then Some (_Js, body)
                    else None
                  end
                in
                (* 極大なものだけ取る *)
                let candidates' =
                  let (<=) (_,p1) (_,p2) = Fpat.(p2 ==> p1) in
                  List.map ~f:fst @@ Fn.maximals' (<=) candidates
                in
                if false then List.iter candidates' ~f:begin fun _Js ->
                  let pss =
                        List.map _Js ~f:begin fun _J ->
                          List.map _J ~f:begin fun j ->
                            List.nth_exn ps j end end
                  in
                  Logs.info begin fun m -> m "I = %a,@ J = %a"
                    Format_.(list_set formula) qs'
                    Format_.(list_set (list_set formula)) pss
                  end
                end;
                let phi's = List.map candidates' ~f:begin fun _Js ->
                    let mk_atom _J =
                          Hfl.mk_apps phi @@
                            List.map one_to_k ~f:begin fun j ->
                              Hfl.Bool (List.mem ~equal:(=) _J j)
                            end
                    in
                    Hfl.mk_ands ~kind:`Inserted
                            @@ List.map xs' ~f:Hfl.mk_var
                             @ List.map _Js ~f:mk_atom
                  end
                in
                Hfl.mk_ors ~kind:`Inserted phi's
              end else begin
                Logs.info begin fun m -> m "I = {%a}, J = {}"
                  Format_.(list ~sep:(fun ppf _ -> string ppf ", ") formula) qs'
                end;
                Hfl.mk_ands @@ List.map ~f:Hfl.mk_var xs'
              end
            end
          in
          (* Format_.print ~tag:"φs" Format_.(list_comma hfl) phi's; *)
          let phi' = Hfl.mk_abss xs @@ Hfl.mk_ors ~kind:`Inserted phi's in
          (* Format_.print ~tag:"φ'" Format_.hfl phi'; *)
          phi'
        end
    | TyArrow({ty = TyInt; _} as x, sigma), TyArrow({ty = TyInt; _} as y, sigma') ->
        let sigma = Subst.Arith.abstraction_ty x (Arith.mk_var y) sigma in
        abstract_coerce env sigma sigma' phi
    | TyArrow({ty = TySigma sigma1 ; _}, sigma2 )
    , TyArrow({ty = TySigma sigma1'; _}, sigma2') ->
        let f = Id.gen ~name:"ac_f" (Type.abstract sigma) in
        let x = Id.gen ~name:"ac_x" (Type.abstract sigma1') in
        let phi1x = abstract_coerce env sigma1' sigma1 (Var x) in
        abstract_coerce env sigma2 sigma2' @@ App(Var f, phi1x)
    | _ -> assert false

let rec abstract_infer : env -> simple_ty Hflz.t -> Type.abstraction_ty * Hfl.t =
  fun env psi ->
    let (sigma, phi) : Type.abstraction_ty * Hfl.t = match psi with
      (* Var *)
      | Var v ->
          let sigma = try IdMap.lookup env v with _ -> assert false in
          (sigma , Var { v with ty = Type.abstract sigma })
      (* Bool *)
      | Bool b ->
          let sigma = TyBool Formula.[Bool b] in
          (sigma, Hfl.mk_identity ATyBool)
      (* Pred-Simple *)
      | Pred(p,as') ->
          let sigma = TyBool Formula.[Pred(p,as')] in
          (sigma, Hfl.mk_identity ATyBool)

      (* Abs-Int *)
      | Abs({ty = TyInt; _} as v, psi) ->
          let (sigma, phi) = abstract_infer env psi in
          (TyArrow(v, sigma), phi)

      | App(psi, Arith a) ->
          begin match abstract_infer env psi with
          | TyArrow({ty = TyInt; _} as x, sigma), phi ->
              (Subst.Arith.abstraction_ty x a sigma, phi)
          | _ -> assert false
          end
      | App(psi1, psi2) ->
          begin match abstract_infer env psi1 with
          | TyArrow({ty = TySigma sigma'; _}, sigma), phi1 ->
              let phi2 = abstract_check env psi2 sigma' in
              (sigma, App(phi1, phi2))
          | _ -> assert false
          end

      (* And, Or *)
      | And(psi1,psi2) | Hflz.Or(psi1,psi2) ->
          let make_ope = match psi with
            | And _ -> fun x y -> Hfl.mk_and x y
            | Or _  -> fun x y -> Hfl.mk_or  x y
            | _     -> assert false
          in
          begin match abstract_infer env psi1, abstract_infer env psi2 with
          | (TyBool preds1, phi1), (TyBool preds2, phi2) ->
              let preds' = List.remove_consecutive_duplicates
                            (List.append preds1 preds2)
                            ~equal:Fpat.(<=>)
              in
              let sigma = TyBool preds' in
              let phi1' = abstract_coerce env (TyBool preds1) sigma phi1 in
              let phi2' = abstract_coerce env (TyBool preds2) sigma phi2 in
              let phi   = merge_lambda (List.length preds') make_ope phi1' phi2' in
              (sigma, phi)
          | _ -> assert false
          end

      | Fix(x, psi, Greatest) ->
          let sigma = try IdMap.lookup env x with _ -> assert false in
          let phi = abstract_check env psi sigma in
          (sigma, Fix({x with ty = Type.abstract sigma}, phi, Greatest))

      | Exists _ | Forall _ | Fix(_,_,Least) -> assert false (* unimplemented *)
      | Abs _ | Arith _ -> assert false (* impossible *)
          (* NOTE Absはpsiがβ-reduxを持たないという仮定の元でimpossible *)
    in
      let phi = Simplify.hfl ~force:false phi in
      Logs.debug begin fun m -> m "@[<0>%a@]@ ==> @[<0>%a@ ⇢ %a@]"
        Format_.(hflz simple_ty_) psi
        Format_.abstraction_ty sigma
        Format_.hfl phi
      end;
      sigma, phi

and abstract_check : env -> simple_ty Hflz.t -> Type.abstraction_ty -> Hfl.t =
  fun env psi sigma ->
    let phi : Hfl.t = match psi, sigma with
      | Abs(x, psi), TyArrow({ty = TySigma sigma'; _}, sigma) ->
          let env' = IdMap.add env x sigma' in
          abstract_check env' psi sigma
      | _ ->
          let sigma', phi = abstract_infer env psi in
          abstract_coerce env sigma' sigma phi
    in
      let phi = Simplify.hfl ~force:false phi in
      Logs.debug begin fun m -> m "@[<0>%a@]@ <== @[<0>%a@ ⇢ %a@]"
        Format_.(hflz simple_ty_) psi
        Format_.abstraction_ty sigma
        Format_.hfl phi
      end;
      phi

let abstract : env -> simple_ty Hflz.t -> Hfl.t =
  fun env psi ->
    let sigma, phi = abstract_infer env psi in
    match sigma with
    | TyBool ps ->
        let complement = Formula.(mk_not (mk_ors ps)) in
        let ps' =
          if Fpat.(complement ==> Formula.Bool false)
          then ps
          else complement::ps
        in
        phi
        |> abstract_coerce env (TyBool ps ) (TyBool ps')
        |> abstract_coerce env (TyBool ps') (TyBool [])
    | _ -> assert false
(* let abstract : env -> simple_ty Hflz.t -> Hfl.t = *)
(*   fun env psi -> abstract_check env psi (TyBool []) *)

