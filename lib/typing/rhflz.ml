open Rethfl_util
open Rethfl_syntax
open Id
open Rtype

type t =
  | Bool   of bool
  | Var    of Rtype.t Id.t
  (* template is used for tracking counterexample. *)
  | Or     of t * t * template * template
  | And    of t * t * template * template
  | Abs    of Rtype.t Id.t * t
  | App    of t * t * template
  | Forall of Rtype.t Id.t * t * template
  (* constructers only for hflz *)
  | Arith  of Arith.t
  | Pred   of Formula.pred * Arith.t list

let rec pp_formula ppf = function
  | Bool x when x -> Fmt.string ppf "tt"
  | Bool _ -> Fmt.string ppf "ff"
  | Var x -> Fmt.string ppf @@ Id.to_string x
  | Or (x, y, _, _) ->
    Fmt.pf ppf "(@[<hov 1>%a@ || %a@])" pp_formula x pp_formula y
  | And (x, y, tx, ty) ->
    Fmt.pf ppf "(@[<hov 1>%a:%a@ && %a:%a@])"
      pp_formula x pp_template tx pp_formula y pp_template ty
  | Abs (x, y) ->
    Fmt.pf ppf "(@[<1>\\%a.@,%a@])" pp_rtype x.ty pp_formula y
  | Forall (x, y, _) ->
    Fmt.pf ppf "(@[<1>∀%a.@,%a@])" pp_rtype x.ty pp_formula y
  | App (x, y, _) ->
    Fmt.pf ppf "(@[<1>%a  %a@])" pp_formula x pp_formula y
  | Arith x -> Fmt.pf ppf "(%a)" Print.arith x
  | Pred (x,[f1; f2]) ->
    Fmt.pf ppf "(%a%a%a)" Print.arith f1 Print.pred x Print.arith f2
  | Pred (x,_) -> Print.pred ppf x

let print_formula f =
  pp_formula Fmt.stdout f;
  Fmt.flush Fmt.stdout ()

let rec is_simple p = match p with
  | And(x, y, _, _) | Or(x, y, _, _) -> (is_simple x && is_simple y)
  | Arith(_) | Var(_) | App(_) | Abs(_) | Forall(_) -> false
  | _ -> true

exception TriedToNegateApp
let rec negate p = match p with
  | Arith(_) | Var(_) | App(_) | Abs(_) | Forall(_) -> raise TriedToNegateApp
  | Or(x, y, t1, t2) -> And(negate x, negate y, t1, t2)
  | And(x, y, t1, t2) -> Or(negate x, negate y, t1, t2)
  | Bool x -> Bool (not x)
  | Pred(p, l) -> Pred(Formula.negate_pred p, l)

let rec translate_if hflz = match hflz with
  | Or(And(a, b, s1, s2), And(a', b', s1',s2'), t1, t2) ->
    let fa = is_simple a in
    let fa' = is_simple a' in
    let fb = is_simple b in
    let fb' = is_simple b' in
    if fa && fa' && negate a = a' then
      And(Or(a', translate_if b, s1, s2), Or(a, translate_if b', s1', s2'), t1, t2)
    else if fa && fb' && negate a = b' then
      And(Or(b', translate_if b, s1, s2), Or(a, translate_if a', s1', s2'), t1, t2)
    else if fb && fa' && negate b = a' then
      And(Or(a', translate_if a, s1, s2), Or(b, translate_if b', s1', s2'), t1, t2)
   else if fb && fb' && negate b = b' then
      And(Or(b', translate_if a, s1, s2), Or(b, translate_if a', s1', s2'), t1, t2)
    else 
      Or(And(translate_if a, translate_if b, s1, s2), And(translate_if a', translate_if b', s1', s2'), t1, t2)
  | Or(x, y, t1, t2) -> Or(translate_if x, translate_if y, t1, t2)
  | And(x, y, t1, t2) -> And(translate_if x, translate_if y, t1, t2)
  | Abs (x, t) -> Abs(x, translate_if t)
  | x -> x

type hes_rule =
  { var  : Rtype.t Id.t
  ; body : t
  ; fix  : Fixpoint.t
  }

let lookup_rule f hes =
  List.find_exn hes ~f:(fun r -> Id.eq r.var f)

let rec replace_rule f rule hes = match hes with
  | [] -> failwith "Not found"
  | rule'::xs when Id.eq rule'.var rule.var
    -> rule::xs
  | rule'::xs -> rule'::replace_rule f rule xs

type hes = hes_rule list

let rec bottom_hflz = function
  | Rtype.RBool _ -> Bool(false)
  | Rtype.RArrow(x, y) -> 
    Abs(Id.gen x, bottom_hflz y)
  | Rtype.RInt(RId(x)) -> Var({x with ty=Rtype.(RInt(RId(x)))})
  | Rtype.RInt(RArith(x)) -> Arith(x)

let rec top_hflz = function
  | Rtype.RBool _ -> Bool(true)
  | Rtype.RArrow(x, y) -> 
    Abs(Id.gen x, top_hflz y)
  | Rtype.RInt(RId(x)) -> Var({x with ty=Rtype.(RInt(RId(x)))})
  | Rtype.RInt(RArith(x)) -> Arith(x)

let rec fvs = function
  | Var x              -> IdSet.singleton x
  | Bool _             -> IdSet.empty
  | Or (phi1,phi2,_,_) -> IdSet.union (fvs phi1) (fvs phi2)
  | And(phi1,phi2,_,_) -> IdSet.union (fvs phi1) (fvs phi2)
  | App(phi1,phi2,_)   -> IdSet.union (fvs phi1) (fvs phi2)
  | Abs(x,phi)         -> IdSet.remove (fvs phi) x
  | Forall (x,phi,_)   -> IdSet.remove (fvs phi) x
  | Arith a            -> IdSet.of_list @@ List.map ~f:Id.remove_ty @@ Arith.fvs a
  | Pred (_,as')       -> IdSet.union_list @@ List.map as' ~f:begin fun a ->
                        IdSet.of_list @@ List.map ~f:Id.remove_ty @@ Arith.fvs a
                      end
