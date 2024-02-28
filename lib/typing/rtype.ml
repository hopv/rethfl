open Hflmc2_syntax
open Rid
open Rresult

type rint =
  | RId of [`Int] Id.t
  | RArith of Arith.t
type rlist =
  | RLId of [`List] Id.t
  | RLsArith of Arith.lt
and t 
  = RBool of refinement
  | RArrow of t * t
  | RInt of rint
  | RList of rlist
and refinement
  = RTrue
   | RFalse
   | RPred of Formula.pred * Arith.t list
   | RLsPred of Formula.ls_pred * Arith.lt list
   | RAnd of refinement * refinement
   | ROr of refinement * refinement
   | RExists of [`Int | `List] Id.t * refinement
   | RTemplate of template
and template = id * Arith.t list * Arith.lt list (* template prdicate name and its args *)

type rprim = 
  | RIntP of rint
  | RListP of rlist

let id_source = ref 0
let id_top = 0
let created = ref false
let generate_id () = id_source := !id_source + 1; !id_source


let rec generate_template_vars = function
  | [] -> ([], [])
  | {Id.ty = `Int;_} as id :: tl -> 
    let (avars, lvars) = generate_template_vars tl in
    let avar = Arith.Var(id) in
    (avar :: avars, lvars)
  | {Id.ty = `List;_} as id :: tl ->
    let (avars, lvars) = generate_template_vars tl in
    let lvar = Arith.LVar(id) in
    (avars, lvar :: lvars)

let generate_template args = 
  let (avars, lvars) = generate_template_vars args in 
  (generate_id(), avars, lvars)
let generate_top_template args  = 
  if !created then
    failwith "You attempted to create top template twice"
  else
    created := true;
    (id_top, args)

(* let generate_rtemplate args = RTemplate(generate_id(), args) *)

let rec clone_type_with_new_pred ints lists = function
  | RBool(RTemplate(_, _, _)) -> RBool(RTemplate(generate_id (), ints, lists))
  | RArrow(RInt(RId(id)), y) ->
    RArrow(RInt(RId(id)), clone_type_with_new_pred (Arith.Var(id)::ints) lists y) 
  | RArrow(RList(RLId(id)), y) ->
    RArrow(RList(RLId(id)), clone_type_with_new_pred ints (Arith.LVar(id)::lists) y) 
  | RArrow(x, y) -> 
    RArrow(clone_type_with_new_pred ints lists x, clone_type_with_new_pred ints lists y)
  | x -> x


let pp_comma : unit Fmt.t = fun ppf () -> Fmt.string ppf ","

let pp_template ppf (id, l, ls) = 
  Fmt.pf ppf "@[X%d(@[<hv 0>%a@];@[<hv 0>%a@])@]"
    id
    (Fmt.list ~sep:pp_comma Print.arith) l
    (Fmt.list ~sep:pp_comma Print.ls_arith) ls
let print_template : template -> unit = fun (id, x, ls) ->
  pp_template Fmt.stdout (id, x, ls);
  Fmt.flush Fmt.stdout ()

let pp_rint ppf = function
  | RId x -> 
    Print.id ppf x
  | RArith x -> 
    Print.arith ppf x
let pp_rlist ppf = function
  | RLId x -> 
    Print.id ppf x
  | RLsArith x -> 
    Print.ls_arith ppf x

let rtype_pred : Formula.pred Fmt.t =
  fun ppf pred -> match pred with
    | Eq  -> Fmt.string ppf "="
    | Neq -> Fmt.string ppf "!="
    | Le  -> Fmt.string ppf "<="
    | Ge  -> Fmt.string ppf ">="
    | Lt  -> Fmt.string ppf "<"
    | Gt  -> Fmt.string ppf ">"
  
let rtype_ls_pred : Formula.ls_pred Fmt.t =
  fun ppf pred -> match pred with
    | Eql  -> Fmt.string ppf "=l"
    | Neql -> Fmt.string ppf "!=l"

let rec pp_refinement prec ppf = function
  | RTrue -> Fmt.string ppf "true"
  | RFalse -> Fmt.string ppf "false"
  | RPred (x, [f1; f2]) -> 
    Print.show_paren (prec > Print.Prec.eq) ppf "@[<hv 0>%a@ %a@ %a@]"
      Print.arith f1
      rtype_pred x
      Print.arith f2
  | RPred (x, _) -> 
    rtype_pred ppf x
  | RLsPred (x, [f1; f2]) -> 
    Print.show_paren (prec > Print.Prec.eq) ppf "@[<hv 0>%a@ %a@ %a@]"
      Print.ls_arith f1
      rtype_ls_pred x
      Print.ls_arith f2
  | RLsPred (x, _) -> 
    rtype_ls_pred ppf x
  | RAnd(x, y) -> 
    Print.show_paren (prec > Print.Prec.and_) ppf "@[<hv 0>%a@ /\\ %a@]"
      (pp_refinement Print.Prec.and_) x
      (pp_refinement Print.Prec.and_) y
  | ROr(x, y) -> 
    Print.show_paren (prec > Print.Prec.or_) ppf "@[<hv 0>%a@ \\/ %a@]"
      (pp_refinement Print.Prec.or_) x
      (pp_refinement Print.Prec.or_) y
  | RExists (x, f) -> 
    Print.show_paren (prec > Print.Prec.abs) ppf "@[<1>∃%a.@,%a@]"
      Print.id x
      (pp_refinement Print.Prec.abs) f
  | RTemplate t -> pp_template ppf t

let rec pp_rtype prec ppf = function
  | RBool r -> begin
    if prec = Print.Prec.(succ arrow) then Fmt.string ppf "(";
    Fmt.pf ppf "bool[@[<1>%a@]]"
      (pp_refinement Print.Prec.zero) r;
    if prec = Print.Prec.(succ arrow) then Fmt.string ppf ")";
  end
  | RArrow(x, y) ->
    Print.show_paren (prec > Print.Prec.arrow) ppf "@[<1>%a ->@ %a@]"
      (pp_rtype Print.Prec.(succ arrow)) x
      (pp_rtype Print.Prec.arrow) y
  | RInt x ->
    Fmt.pf ppf "@[%a:int@]"
      pp_rint x
  | RList x ->
    Fmt.pf ppf "@[%a:list@]"
      pp_rlist x

let print_rtype x =
  pp_rtype (Print.Prec.zero) Fmt.stdout x;
  Fmt.flush Fmt.stdout ()

let print_refinement x =
  pp_refinement (Print.Prec.zero) Fmt.stdout x;
  Fmt.flush Fmt.stdout ()
  
let rint2arith = function
  | RId x -> Arith.Var(x)
  | RArith x -> x

let conjoin x y =
  if x = RTrue then y
  else if y = RTrue then x
  else if x = RFalse then RFalse
  else if y = RFalse then RFalse
  else RAnd(x, y)

let disjoin x y =
  if x = RFalse then y
  else if y = RFalse then x
  else if x = RTrue then RTrue
  else if y = RTrue then RTrue
  else ROr(x, y)


let subst_ariths id rint l = match rint with 
  | RId id' -> 
    List.map (Trans.Subst.Arith.arith id (Arith.Var(id'))) l
  | RArith a ->
    List.map (Trans.Subst.Arith.arith id a) l

let subst_ls_ariths id rlist ls = match rlist with 
  | RLId id' -> 
    List.map (Trans.Subst.Arith.ls_arith id (Arith.LVar(id'))) ls
  | RLsArith a ->
    List.map (Trans.Subst.Arith.ls_arith id a) ls

let rec subst_refinement id (rprim:rprim) refinement = 
  match (rprim, refinement) with
  | (RIntP(rint), RPred (p, l)) -> RPred(p, subst_ariths id rint l)
  | (RListP(rlist), RLsPred (p, l)) -> RLsPred(p, subst_ls_ariths id rlist l)
  | (_, RAnd(x, y)) -> conjoin (subst_refinement id rprim x) (subst_refinement id rprim y)
  | (_, ROr(x, y)) -> ROr(subst_refinement id rprim x, subst_refinement id rprim y)
  | (RIntP(rint), RTemplate(id', l, ls)) -> RTemplate(id', subst_ariths id rint l, ls)
  | (RListP(rlist), RTemplate(id', l, ls)) -> RTemplate(id', l, subst_ls_ariths id rlist ls)
  | (_, x) -> x

let rec subst id rprim = function
  | RBool r -> RBool(subst_refinement id rprim r)
  | RArrow(x, y) -> RArrow(subst id rprim x, subst id rprim y)
  | RInt x -> RInt x
  | RList x -> RList x

(* tuple of ids of substitution *)
let rec subst_refinement_with_ids body l = match l with
  | [] -> body
  | (x, y):: xs -> 
    subst_refinement_with_ids (subst_refinement x y body) xs

(* check if refinement contains template *)
let rec does_contain_pred = function 
  | RTemplate _ -> true
  | RAnd(x, y) | ROr(x, y) -> does_contain_pred x || does_contain_pred y
  | _ -> false
  
let rec count_preds = function 
  | RTemplate _ -> 1
  | RAnd(x, y) | ROr(x, y) -> count_preds x + count_preds y
  | _ -> 0


(* returns not formula. Negating template is illegal, so throws execption *)
exception TriedToNegateTemplate
let rec negate_ref = function
  | RTemplate _ -> raise TriedToNegateTemplate
  | RAnd(x, y) -> ROr(negate_ref x, negate_ref y)
  | ROr(x, y) -> RAnd(negate_ref x, negate_ref y)
  | RTrue -> RFalse
  | RFalse -> RTrue
  | RPred(p, l) -> RPred(Formula.negate_pred p, l)
  | RLsPred(p, l) -> RLsPred(Formula.negate_ls_pred p, l)

let rec dual = function
  | RTemplate x -> RTemplate x
  | RAnd(x, y) -> ROr(dual x, dual y)
  | ROr(x, y) -> RAnd(dual x, dual y)
  | RTrue -> RFalse
  | RFalse -> RTrue
  | RPred(p, l) -> RPred(Formula.negate_pred p, l)
  | RLsPred(p, l) -> RLsPred(Formula.negate_ls_pred p, l)

(* This is an adhoc optimization of formulas. The reason why this function is required is
that consider following program and its safety property problem.

[Program]
(* the definition of f and g is omitted *)
let h x = if x >= 0 then g x else f x
let m n = assert(h n)
[HES Formula]
H x =v (x >= 0 /\ G x) \/ (x < 0 /\ F x)
S n =v H n

Then this formula will generate chc formulas, at least one of which has a head which contains 
more than one or.
To remedy this problem, the above "gadget" of formula can automatically be translated to the following.
H x =v (x < 0 \/ G x) /\ (x >= 0 /\ F x)
S n =v H n
And this is what The following function does.

And for the speed of translation, I did not use the complete algorithm for this, just checking 
the negation of one formula is equal to the other.
*)

let rec translate_if = 
  function
  | ROr(RAnd(a, b), RAnd(a', b')) ->
    let fa = does_contain_pred a |> not in
    let fb = does_contain_pred b |> not in
    let fa' = does_contain_pred a' |> not in
    let fb' = does_contain_pred b' |> not in
    if fa && fa' && negate_ref a = a' then
      RAnd(ROr(a', translate_if b), ROr(a, translate_if b'))
    else if fa && fb' && negate_ref a = b' then
      RAnd(ROr(b', translate_if b), ROr(a, translate_if a'))
    else if fb && fa' && negate_ref b = a' then
      RAnd(ROr(a', translate_if a), ROr(b, translate_if b'))
   else if fb && fb' && negate_ref b = b' then
      RAnd(ROr(b', translate_if a), ROr(b, translate_if a'))
    else 
      ROr(RAnd(translate_if a, translate_if b), RAnd(translate_if a', translate_if b'))
  | ROr(x, y) -> ROr(translate_if x, translate_if y)
  | RAnd(x, y) -> RAnd(translate_if x, translate_if y)
  | x -> x


let rec to_bottom = function 
  | RArrow(x, y) -> RArrow(to_top x, to_bottom y)
  | RBool _ -> RBool RFalse
  | RInt(x) -> RInt(x)
  | RList(x) -> RList(x)
and to_top = function
  | RArrow(x, y) -> RArrow(to_bottom x, to_top y)
  | RBool _ -> RBool RTrue
  | RInt(x) -> RInt(x)
  | RList(x) -> RList(x)
let rec get_top = function
  | RBool(RTemplate(x)) -> x
  | RArrow(_, s) -> get_top s
  | _ -> failwith "program error" (* should not occur int *)

let rec simplify x = match x with
  | RPred(p, l) -> begin match Formula.simplify_pred p l with 
    | Some(true) -> RTrue
    | Some(false) -> RFalse
    | None -> x
    end
  | RAnd(x, y) -> 
    let x' = simplify x in
    let y' = simplify y in
    conjoin x' y'
  | ROr(x, y) -> 
    let x' = simplify x in
    let y' = simplify y in
    disjoin x' y'
  | x -> x