open Hflmc2_util

type op =
  | Add
  | Sub
  | Mult
  | Div
  | Mod
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* arithmetic expresion parametrized by variable type *)
type 'var gen_t =
  | Int of int
  | Var of 'var
  | Op  of op * 'var gen_t list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type t = [`Int] Id.t gen_t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type ('avar, 'lvar) gen_lt =
  | Nil
  | Cons of 'avar gen_t * ('avar, 'lvar) gen_lt
  | LVar of 'lvar
  [@@deriving eq,ord,show,iter,map,fold,sexp]
type lt = ([`Int] Id.t, [`List] Id.t) gen_lt
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_int n     = Int(n)
let mk_nil       = Nil
let mk_cons hd tl  = Cons(hd,tl)
let mk_op op as' = Op(op,as')
let mk_var' v    = Var v
(* specific to [t] *)
let mk_var v : t = Var({v with ty = `Int})

let mk_lvar v : lt = LVar({v with ty = `List})

let rec fvs : 'var gen_t -> 'var list = function
  | Int _ -> []
  | Var v -> [v]
  | Op (_, as') -> List.concat_map as' ~f:fvs

let rec lfvs : ('avar, 'lvar) gen_lt -> 'avar list * 'lvar list = function
  | Nil -> [], []
  | Cons (hd, tl) -> 
    let (avss, lvss) = lfvs tl in
    List.append (fvs hd) avss, lvss
  | LVar v -> [], [v]

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
  | _ -> failwith "evaluation error"
