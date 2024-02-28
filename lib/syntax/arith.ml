open Hflmc2_util

type op =
  | Add
  | Sub
  | Mult
  | Div
  | Mod
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* codomain: List *)
type opl =
  | Nil
  | Cons
  | Tail
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* List -> Int *)
type size =
  | Length
  | Head
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* arithmetic expresion parametrized by variable type *)
type ('avar, 'lvar) gen_t =
  | Int of int
  | Var of 'avar
  | Op  of op * ('avar, 'lvar) gen_t list
  | Size of size * ('avar, 'lvar) gen_lt
  [@@deriving eq,ord,show,iter,map,fold,sexp]
and ('avar, 'lvar) gen_lt =
  | Opl of opl * ('avar, 'lvar) gen_t list * ('avar, 'lvar) gen_lt list
  | LVar of 'lvar
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type t = ([`Int] Id.t, [`List] Id.t) gen_t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type lt = ([`Int] Id.t, [`List] Id.t) gen_lt
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_int n     = Int(n)
let mk_nil       = Opl(Nil, [], [])
let mk_cons hd tl  = Opl(Cons, [hd], [tl])
let mk_tail ls  = Opl(Tail, [], [ls])
let mk_op op as' = Op(op,as')
let mk_var' v    = Var v
(* specific to [t] *)
let mk_var v : t = Var({v with ty = `Int})

let mk_lvar v : lt = LVar({v with ty = `List})

let product f g (a, b) = (f a, g b) 

let rec fold_two_lists = function
  | [] -> ([],[])
  | (a1, a2)::xs ->
  let (b1, b2) = fold_two_lists xs in
  (List.append a1 b1, List.append a2 b2)

let rec fvs : ('avar, 'lvar) gen_t -> 'avar list * 'lvar list = function
  | Int _ -> [], []
  | Var v -> [v], []
  | Op (_, as') -> 
    let v = List.map as' ~f:fvs in
    fold_two_lists v
  | Size (_, ls) -> lfvs ls
and lfvs : ('avar, 'lvar) gen_lt -> 'avar list * 'lvar list = function
  | Opl (_, as', ls') -> 
    let fvs1 = List.map ~f:fvs as' in
    let fvs2 = List.map ~f:lfvs ls' in
    let fvs = fvs1 @ fvs2 in
    fold_two_lists fvs
  | LVar v -> [], [v]

let fvs_of_ariths as' = 
  let v = List.map as' ~f:fvs in
    fold_two_lists v

let fvs_of_lists as' = 
  let v = List.map as' ~f:lfvs in
    fold_two_lists v

let fvs_notype t = 
  let (vs1, vs2) = fvs t in
  let (vs1, vs2) = (List.map ~f:Id.remove_ty vs1, List.map ~f:Id.remove_ty vs2) in
  List.append vs1 vs2

let lfvs_notype t = 
  let (vs1, vs2) = lfvs t in
  let (vs1, vs2) = (List.map ~f:Id.remove_ty vs1, List.map ~f:Id.remove_ty vs2) in
  List.append vs1 vs2

let lift f x y = match (x, y) with
  | Some(x), Some(y) -> Some(f x y)
  | _ -> None

let op_func = function 
  | Add -> (+)
  | Sub -> (-)
  | Mult -> ( * )
  | Div -> (/)
  | Mod -> (mod)

let rec evaluate_opt x = match x with
  | Op(op, x::xs) -> 
  List.fold ~init:(evaluate_opt x) ~f:(lift @@ op_func op) (List.map ~f:evaluate_opt xs)
  | Var _ -> None
  | Int(x) -> Some(x)
  | Size _ -> None
  | _ -> failwith "evaluation error"
