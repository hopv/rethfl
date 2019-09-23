open Hflmc2_util
open Hflmc2_syntax
module Options = Hflmc2_options.Abstraction
module FpatInterface = FpatInterface

let log_src = Logs.Src.create
    ~doc:"Int-based Predicate Abstraction"
    "Abstraction.Int_base"
module Log = (val Logs.src_log log_src)

module IType = struct
  type abst_arg_ty
    = TyInt   of Formula.t list
    | TySigma of abst_ty
    [@@deriving eq,ord,show,iter,map,fold,sexp]
  and abst_ty =
    | TyBool
    | TyArrow of abst_arg_ty Id.t * abst_ty

  let mk_arrows : abst_arg_ty Id.t list -> abst_ty =
    fun args ->
      List.fold_right args ~init:TyBool ~f:begin fun arg ret_ty ->
        TyArrow(arg, ret_ty)
      end

  let rec merge =
    fun append ty1 ty2 -> match ty1, ty2 with
      | TyBool, TyBool -> TyBool
      | TyArrow ({ty=TyInt preds1;_} as x1, rty1)
      , TyArrow ({ty=TyInt preds2;_} as x2, rty2) when Id.eq x1 x2 ->
          TyArrow ( {x1 with ty = TyInt (append preds1 preds2)}
                  , merge append rty1 rty2 )
      | TyArrow ({ty=TySigma aty1;_} as x1, rty1)
      , TyArrow ({ty=TySigma aty2;_} as x2, rty2) when Id.eq x1 x2 ->
          TyArrow
            ( {x1 with ty = TySigma (merge append aty1 aty2)}
            , merge append rty1 rty2 )
      | _ -> invalid_arg "Type.merge"
  let merges = fun append tys ->
    match tys with
    | [] -> invalid_arg "Type.merges"
    | ty::tys -> List.fold_right ~init:ty tys ~f:(merge append)

  let rec pp_hum_ =
    fun prec ppf ty -> match ty with
      | TyBool -> Fmt.pf ppf "bool"
      | TyArrow (x, ret) ->
          let open Print in
          show_paren (prec > Prec.arrow) ppf "@[<1>%a:%a ->@ %a@]"
            id x
            (pp_hum_arg_ (Prec.(succ arrow))) x.ty
            (pp_hum_ Prec.arrow) ret
  and pp_hum_arg_ =
    fun prec ppf argty -> match argty with
      | TyInt preds ->
          Print.(pf ppf "int[%a]"
            (list ~sep:semicolon formula) preds)
      | TySigma ty -> pp_hum_ prec ppf ty
  let pp_hum = pp_hum_ Print.Prec.zero

  let rec abstract : abst_ty -> Type.abstracted_ty = function
    | TyBool -> ATyBool
    | TyArrow({ Id.ty = TyInt preds; _ }, ret) ->
        Fn.apply_n_times ~n:(List.length preds)
          (fun ret -> Type.ATyArrow(ATyBool, ret))
          (abstract ret)
    | TyArrow({ Id.ty = TySigma arg; _}, ret) ->
        ATyArrow(abstract arg, abstract ret)

  let rec of_bool_base : ?bounded:[`Int] Id.t list -> Type.abstraction_ty -> abst_ty =
    fun ?(bounded=[]) bty ->
      let args, preds = Type.decompose_arrow bty in
      let rec go rev_args bounded xs preds = match xs with
        | [] ->
            if preds=[] then List.rev rev_args else begin
              Log.err begin fun m -> m "@[<v>%a@;%a@]"
                Print.(list_comma formula) preds
                Print.(list_comma id) bounded
              end;
              Fn.fatal "of_bool_base"
            end
        | (Id.{ty=Type.TyInt;_} as x)::xs ->
            let bounded = {x with ty=`Int}::bounded in
            let captured, rest =
              List.partition_tf preds ~f:begin fun p ->
                List.subset (snd @@ Formula.fvs p) bounded
              end
            in
            let x = { x with ty = TyInt captured } in
            go (x::rev_args) bounded xs rest
        | (Id.{ty=Type.TySigma sigma;_} as x)::xs ->
            let x = { x with ty = TySigma (of_bool_base ~bounded sigma) } in
            go (x::rev_args) bounded xs preds
      in
      mk_arrows (go [] bounded args preds)

  module Subst = struct
    let rec arith : unit Id.t -> Arith.t -> abst_ty -> abst_ty =
      fun x a sigma -> match sigma with
        | TyBool -> TyBool
        | TyArrow (arg, ret) ->
            TyArrow ( { arg with ty = arith_arg x a arg.ty }
                    , arith x a ret)
    and arith_arg : unit Id.t -> Arith.t -> abst_arg_ty -> abst_arg_ty =
      fun x a sigma -> match sigma with
        | TyInt preds ->
            TyInt (List.map preds ~f:(Trans.Subst.Arith'.formula x a))
        | TySigma sigma ->
            TySigma (arith x a sigma)
    let arith : 'a. 'a Id.t -> Arith.t -> abst_ty -> abst_ty =
      fun x a sigma -> arith (Id.remove_ty x) a sigma
  end
end

module FormulaSet = Set.Make(Formula)
type preds_set = FormulaSet.t

type gamma = IType.abst_ty IdMap.t

type env =
  { gamma     : gamma
  ; preds_set : preds_set
  ; guard     : Formula.t
  }

let name_of_formulas : (Formula.t, Type.abstracted_ty Id.t) Hashtbl.t =
  Hashtbl.create (module Formula)
let name_of f =
  let if_found x = x in
  let if_not_found _ =
    let b = Id.gen ~name:"b" Type.ATyBool in
    if false then Log.debug begin fun m -> m ~header:"name_of_formulas" "%a[%a]"
      Print.id b Print.formula f
    end;
    Hashtbl.add_exn name_of_formulas ~key:f ~data:b;
    b
  in Hashtbl.find_and_call name_of_formulas f ~if_found ~if_not_found
let reset_name_of_formulas() = Hashtbl.clear name_of_formulas

let pp_gamma : IType.abst_ty IdMap.t Print.t =
  fun ppf gamma ->
    let compare_id (x,_) (y,_) = compare x.Id.id y.Id.id in
    let item ppf (f,aty) =
      Print.pf ppf "@[<h>%a : %a@]" Print.id f IType.pp_hum aty
    in
    Print.pf ppf "@[<v>%a@]"
      (Print.list item)
      (List.sort ~compare:compare_id @@ IdMap.to_alist gamma)
let pp_preds =
  fun ppf preds ->
    let item ppf f =
      Print.pf ppf "@[<h>%a[%a]@]"
        Print.id (name_of f)
        Print.formula f
    in
    Print.pf ppf "@[<h>%a@]"
      Print.(list_set item) (FormulaSet.to_list preds)
let pp_env : env Print.t =
  fun ppf env ->
    Print.pf ppf "%a | %a "
      pp_preds env.preds_set
      Print.formula env.guard

let merge_types tys =
  let append_preds ps qs =
    List.remove_duplicates ~equal:FpatInterface.(<=>) @@ (ps@qs)
  in IType.merges append_preds tys

let merge_gamma =
  fun gamma1 gamma2 ->
    IdMap.merge gamma1 gamma2
      ~f:begin fun ~key:_ -> function
      | `Left l -> Some l
      | `Right r -> Some r
      | `Both (l, r) -> Some (merge_types [l;r])
      end

let rec infer_type
          : env
         -> Type.simple_ty Hflz.t
         -> IType.abst_ty * FormulaSet.t =
  fun env psi -> match psi with
    | Bool _ -> TyBool, FormulaSet.empty
    | Var x  -> IdMap.lookup env.gamma x, FormulaSet.empty
    | Pred(p,as') -> TyBool, FormulaSet.singleton (Pred(p,as'))
    | App(psi1, Arith a) ->
        begin match infer_type env psi1 with
        | IType.TyArrow({ty = TyInt preds;_} as x, ret_ty), preds_set ->
            IType.Subst.arith x a ret_ty,
            FormulaSet.(union
              (map ~f:(Trans.Subst.Arith'.formula x a) preds_set)
              (of_list (List.map ~f:(Trans.Subst.Arith'.formula x a) preds)))
        | _ -> assert false
        end
    | App(psi1,_) ->
        begin match infer_type env psi1 with
        | TyArrow(_,ret_ty), preds_set -> ret_ty, preds_set
        | _ -> assert false
        end
    | Or(psi1,psi2) | And(psi1,psi2) ->
        let ty1, preds_set1 = infer_type env psi1 in
        let ty2, preds_set2 = infer_type env psi2 in
        merge_types [ty1;ty2], FormulaSet.union preds_set1 preds_set2
    | _ -> Fn.fatal "impossible"
    (* Arith | Abs *)

(* Γ | C ⊢ φ : (Φ1,σ1)≤(Φ2,σ2) ↝  φ' *)
let rec abstract_coerce
          : Formula.t
         -> Hfl.t
         -> preds_set * IType.abst_ty
         -> preds_set * IType.abst_ty
         -> Hfl.t =
  fun guard phi (preds_set,sigma) (preds_set',sigma') ->
    let phi' = match sigma, sigma' with
      | TyBool, TyBool
          when FormulaSet.(is_empty (diff preds_set preds_set')) -> phi
      | TyBool, TyBool ->
          let ps = FormulaSet.to_list preds_set  in
          let qs = FormulaSet.to_list preds_set' in
          let l = List.length qs in
          let k = List.length ps in
          let one_to_l = List.(range 0 l) in (* to be honest, 0 to l-1 *)
          let one_to_k = List.(range 0 k) in
          let _Is = List.powerset one_to_l in
          let phi's =
            let _IJs =
              List.map _Is ~f:begin fun _I ->
                let qs' = List.(map ~f:(nth_exn qs) _I) in
                let _Q  = Formula.mk_ands (guard::qs') in
                (* Q => \/i(/\Ji) を満たす極大の J1,...,Jh の集合を得る *)
                let _Jss =
                  if FpatInterface.(_Q ==> Formula.Bool false) then
                    [[one_to_k]] (* /\{P1,...,Pk}が唯一の極大元 *)
                  else if FpatInterface.is_valid _Q then
                    [FpatInterface.min_valid_cores ps]
                  else
                    [FpatInterface.strongest_post_cond _Q ps]
                in
                (_I, _Jss)
              end
            in
            let _IJs = _IJs
              (* Group by equality of Jss *)
              |> List.sort ~compare:Fn.(on snd compare)
              |> List.group ~break:Fn.(on snd (<>))
              (* Remove I which has its subset in the same group *)
              |> List.concat_map ~f:Fn.(maximals' (on fst (flip List.subset)))
            in
            List.map _IJs ~f:begin fun (_I,_Jss) ->
              let conjunctions =
                List.map _Jss ~f:begin fun _Js ->
                  let mk_var i = Hfl.mk_var (name_of @@ List.nth_exn qs i) in
                  let mk_atom _J =
                    let subst =
                      List.map one_to_k ~f:begin fun j ->
                        name_of (List.nth_exn ps j),
                        Hfl.Bool (List.mem ~equal:(=) _J j)
                      end
                    in
                    Trans.Subst.Hfl'.hfl (IdMap.of_list subst) phi
                  in
                  Hfl.mk_ands ~kind:`Inserted
                   @@ List.map _I ~f:mk_var
                    @ List.map _Js ~f:mk_atom
                end
              in
              Hfl.mk_ors ~kind:`Inserted conjunctions
            end
          in Hfl.mk_ors ~kind:`Inserted phi's
      | TyArrow({ty=TyInt preds ;_} as x , sigma )
      , TyArrow({ty=TyInt preds';_} as x', sigma') ->
          let preds = List.map preds
            ~f:(Trans.Subst.Id'.formula (IdMap.singleton x {x' with ty=`Int}))
          in
          let sigma = IType.Subst.arith x (Arith.mk_var x') sigma in
          Hfl.mk_abss (List.map ~f:name_of preds') @@
            abstract_coerce guard
              Hfl.(mk_apps phi (List.map ~f:(mk_var<<<name_of) preds))
                (FormulaSet.(union preds_set  (of_list preds )), sigma )
                (FormulaSet.(union preds_set' (of_list preds')), sigma')
      | TyArrow({ty=TySigma sigma1 ;_}, sigma2 )
      , TyArrow({ty=TySigma sigma1';_}, sigma2') ->
          let x = Id.gen (IType.abstract sigma1') in
          let phi1 =
            abstract_coerce guard (Hfl.mk_var x)
              (FormulaSet.empty, sigma1')
              (preds_set', sigma1)
          in
          let phi2 =
            abstract_coerce guard (Hfl.mk_app phi phi1)
              (preds_set, sigma2)
              (preds_set', sigma2')
          in Hfl.mk_abs x phi2
      | _ -> Fn.fatal "OMG"
    in
    Log.debug begin fun m -> m ~header:"Term:Coerce"
      "@[<hv 0>%a⊢@;%a@;<1 1>: (%a,%a) ≺@;  (%a,%a)@;<1 0>⇢  %a@]"
        Print.formula guard
        Print.hfl phi
        pp_preds preds_set
        IType.pp_hum sigma
        pp_preds preds_set'
        IType.pp_hum sigma'
        Print.hfl phi'
    end;
    phi'

(* Γ | Φ_in | C ⊢⇑ ψ : σ ↝  φ;Φ_out *)
let rec abstract_infer
          : env
         -> Type.simple_ty Hflz.t
         -> IType.abst_ty * Hfl.t * FormulaSet.t =
  fun env psi ->
    let sigma, phi, preds_set = match psi with
      | Var v ->
          begin try
            let sigma = IdMap.lookup env.gamma v in
            sigma,
            Hfl.Var { v with ty = IType.abstract sigma },
            FormulaSet.empty
          with _ -> Fn.fatal @@
            Fmt.strf "Variable %s not found in environment" (Id.to_string v)
          end
      | Bool b ->
          TyBool,
          Hfl.Bool b,
          FormulaSet.empty
      | Pred(p,as') ->
          let pred = Formula.Pred(p,as') in
          TyBool,
          Hfl.mk_var (name_of pred),
          FormulaSet.singleton pred
      | App(psi, Arith a) ->
          begin match abstract_infer env psi with
          | TyArrow({ty = TyInt preds; _} as x, sigma), phi, preds_set ->
              IType.Subst.arith x a sigma,
              Hfl.mk_apps phi @@ List.map preds
                ~f:(Hfl.mk_var<<<name_of<<<Trans.Subst.Arith'.formula x a),
              FormulaSet.(union preds_set @@ of_list @@
                List.map preds ~f:(Trans.Subst.Arith'.formula x a))
          | _ -> assert false
          end
      | App(psi1, psi2) ->
          begin match abstract_infer env psi1 with
          | TyArrow({ty = TySigma sigma1; _}, sigma2), phi1, preds_set1 ->
              let preds_set = FormulaSet.union env.preds_set preds_set1 in
              let phi2 = abstract_check { env with preds_set } psi2 sigma1 in
              sigma2,
              Hfl.mk_app phi1 phi2,
              preds_set1
          | _ -> assert false
          end
      | And ((Pred(p,as') as psi_s), psi_m)
      | And (psi_m, (Pred(p,as') as psi_s)) ->
          let _, phi_s, preds_set_s = abstract_infer env psi_s in
          let pred = Formula.(Pred(p,as')) in
          let guard = Formula.(mk_and env.guard pred) in
          let preds_set = FormulaSet.remove env.preds_set pred in
          let _, phi_m, preds_set_m =
            abstract_infer { env with guard; preds_set } psi_m
          in
          let reorder = match psi with
            | And (Pred _, _) -> [phi_s;phi_m]
            | And (_, Pred _) -> [phi_m;phi_s]
            | _ -> assert false
          in
          TyBool,
          Hfl.mk_ands reorder ~kind:`Original,
          FormulaSet.union preds_set_m preds_set_s
      | Or ((Pred(p,as') as psi_s), psi_m)
      | Or (psi_m, (Pred(p,as') as psi_s)) ->
          let _, phi_s, preds_set_s = abstract_infer env psi_s in
          let pred = Formula.(mk_not @@ Pred(p,as')) in
          let guard = Formula.(mk_and env.guard pred) in
          let preds_set = FormulaSet.remove env.preds_set pred in
          let _, phi_m, preds_set_m =
            abstract_infer { env with guard; preds_set } psi_m
          in
          let reorder = match psi with
            | Or (Pred _, _) -> [phi_s;phi_m]
            | Or (_, Pred _) -> [phi_m;phi_s]
            | _ -> assert false
          in
          TyBool,
          Hfl.mk_ors reorder ~kind:`Original,
          FormulaSet.union preds_set_m preds_set_s
      | And (psi1,psi2) | Or (psi1,psi2) ->
          let _, preds_set1 = infer_type env psi1 in
          let _, preds_set2 = infer_type env psi2 in
          let preds_set = FormulaSet.union_list
            [ env.preds_set; preds_set1; preds_set2 ]
          in
          let phi1 = abstract_check { env with preds_set } psi1 TyBool in
          let phi2 = abstract_check { env with preds_set } psi2 TyBool in
          TyBool,
          (match psi with
           | And _ -> Hfl.And([phi1;phi2],`Original)
           | Or  _ -> Hfl.Or ([phi1;phi2],`Original) | _ -> assert false),
          FormulaSet.union preds_set1 preds_set2
      | Abs _ | Arith _ -> assert false
    in
      let phi = Trans.Simplify.hfl phi in
      Log.debug begin fun m -> m ~header:"Term:Infer"
          "@[<hv 0>%a⊢@;%a@ ==> %a@;<1 1>⇢  %a; %a@]"
          pp_env env
          Print.(hflz simple_ty_) psi
          IType.pp_hum sigma
          Print.hfl phi
          pp_preds preds_set
      end;
      sigma, phi, preds_set

and abstract_check
      : env
     -> Type.simple_ty Hflz.t
     -> IType.abst_ty
     -> Hfl.t =
  fun env psi sigma ->
    let phi : Hfl.t = match psi, sigma with
      | Abs(x, psi), TyArrow({ty=TySigma sigma1;_}, sigma2) ->
          let gamma = IdMap.add env.gamma x sigma1 in
          let x'  = Id.{ x with ty = IType.abstract sigma1 } in
          Hfl.mk_abs x' @@ abstract_check { env with gamma } psi sigma2
      | Abs({ty=TyInt;_} as x, psi), TyArrow({ty=TyInt preds;_} as x', sigma) ->
          let preds =
            List.map preds ~f:begin fun pred ->
              Trans.Subst.Id'.formula
                (IdMap.singleton x' {x with ty=`Int}) pred
            end
          in
          let sigma = IType.Subst.arith x' (Arith.mk_var x) sigma in
          let preds_set = FormulaSet.(union env.preds_set (of_list preds)) in
          Hfl.mk_abss (List.map ~f:name_of preds) @@
            abstract_check { env with preds_set } psi sigma
      | _ ->
          let sigma', phi, preds_set = abstract_infer env psi in
          let preds_set = FormulaSet.union env.preds_set preds_set in
          abstract_coerce env.guard phi
            (preds_set, sigma')
            (env.preds_set, sigma)
    in
      let phi = Trans.Simplify.hfl phi in
      Log.debug begin fun m -> m ~header:"Term:Check"
        "@[<hv 0>%a⊢@;%a@ <== %a@;<1 1>⇢  %a@]"
          pp_env env
          Print.(hflz simple_ty_) psi
          IType.pp_hum sigma
          Print.hfl phi
      end;
      phi

let abstract_rule : gamma -> Type.simple_ty Hflz.hes_rule -> Hfl.hes_rule =
  fun gamma { var; body; fix } ->
    let env = { gamma; preds_set=FormulaSet.empty; guard=Bool true} in
    let aty = IdMap.lookup gamma var in
    let rule' =
      Hfl.{ var  = Id.{ var with ty = IType.abstract aty }
          ; body = abstract_check env body aty
          ; fix  = fix
          }
    in
    begin Log.debug @@ fun m -> m ~header:"Nonterminal" "%a"
      Print.hfl_hes_rule rule'
    end;
    rule'

let abstract
      : Type.abstraction_ty IdMap.t
     -> Type.simple_ty Hflz.hes
     -> Hfl.hes =
  fun gamma' hes ->
    reset_name_of_formulas();
    let gamma = IdMap.map gamma' ~f:IType.of_bool_base in
    Log.debug begin fun m -> m ~header:"IntEnv" "%a" pp_gamma gamma end;
    List.map ~f:(abstract_rule gamma) hes
