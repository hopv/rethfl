open Hflmc2_syntax
open Rtype
open Fpl

let rec gen_len_args len = 
  if len < 1 then ""
  else if len = 1 then "Int"
  else "Int " ^ gen_len_args (len - 1)

let rec gen_len_ls_args solver len = 
  let tystr = match solver with
  | `Hoice -> "(List Int) "
  | _ -> "List " in
  if len < 1 then ""
  else if len = 1 then tystr
  else tystr ^ gen_len_ls_args solver (len - 1)

let pred_def solver (name, (len1, len2)) =
  gen_len_args len1 ^ " " ^ gen_len_ls_args solver len2 |> Printf.sprintf "(declare-fun %s (%s) Bool)\n" (Rid.to_string name)


let var_def id = id |> Id.to_string |> Printf.sprintf "(%s Int)"
let lvar_def solver id = 
  match solver with
  | `Hoice -> id |> Id.to_string |> Printf.sprintf "(%s (List Int))"
  | _ -> id |> Id.to_string |> Printf.sprintf "(%s List)"

let op2smt2 = 
  let open Arith in
  function
  | Add -> "+"
  | Sub -> "-"
  | Mult -> "*"
  | Div -> "/"
  | Mod -> "%"
let pred2smt2 pred args = 
  let open Formula in
  Printf.sprintf 
  begin
    match pred with
    | Eq -> "(= %s)"
    | Neq -> "(not (= %s))"
    | Le -> "(<= %s)"
    | Ge -> "(>= %s)"
    | Lt -> "(< %s)"
    | Gt -> "(> %s)"
    | Eql -> "(= %s)"
    | Neql -> "(not (= %s))"
  end args

let rec arith2smt2 = 
  let open Arith in
  function 
  | Int x -> Printf.sprintf "%d" x
  | Var id -> Id.to_string id
  | Op (op, l) -> 
    let args = ariths2smt2 l in
    let op_s = op2smt2 op in
    Printf.sprintf "(%s %s)" op_s args
  | Size (Length, ls) -> Printf.sprintf "(_size %s)" (lsexpr2smt2 ls)
  | Size (Head, ls) -> Printf.sprintf "(head %s)" (lsexpr2smt2 ls)
and ariths2smt2 l =
    l |> List.map arith2smt2 |> List.fold_left (fun s x -> s ^ " " ^ x) "" 

and lsexpr2smt2 = 
  let open Arith in
  function 
  | LVar id -> Id.to_string id
  | Opl (Nil, _, _) -> Printf.sprintf "nil"
  | Opl (Cons, [hd], [tl]) -> 
    let head = arith2smt2 hd in
    let tail = lsexpr2smt2 tl in
    Printf.sprintf "(insert %s %s)" head tail
  | Opl (Tail, _, [ls]) ->
    Printf.sprintf "(tail %s)" (lsexpr2smt2 ls)
  | _ -> assert false
and lsexprs2smt2 l =
    l |> List.map lsexpr2smt2 |> List.fold_left (fun s x -> s ^ " " ^ x) "" 
let template2smt2 (p, l, ls) =
  let name = Rid.to_string p in
  let args = ariths2smt2 l in
  let lsargs = lsexprs2smt2 ls in
    if args = "" && lsargs = "" then
      Printf.sprintf "%s" name 
    else
      Printf.sprintf "(%s %s %s)" name args lsargs

let pred2smt2 (p, a, l) =
  let arga = ariths2smt2 a in
  let argl = lsexprs2smt2 l in
  let args = arga ^ " " ^ argl in
  pred2smt2 p args

let rec ref2smt2 rt = match rt with
  | RTrue -> "true"
  | RFalse -> "false"
  | RAnd(x, y) -> Printf.sprintf "(and %s %s)" (ref2smt2 x) (ref2smt2 y)
  | ROr(x, y) -> Printf.sprintf "(or %s %s)" (ref2smt2 x) (ref2smt2 y)
  | RTemplate(p, l, ls) -> template2smt2 (p, l, ls)
  | RPred(p, a, l) -> pred2smt2(p, a, l)
  | RExists _ -> assert false

let rec fpl2smt2 fml = 
  let open Fpl in
  match fml with
  | Bool x when x -> "true"
  | Bool x -> "false"
  | Or(x, y) -> Printf.sprintf "(or %s %s)" (fpl2smt2 x) (fpl2smt2 y)
  | And(x, y) -> Printf.sprintf "(and %s %s)" (fpl2smt2 x) (fpl2smt2 y)
  | Forall(x, y) -> 
    Printf.sprintf "(forall ((%s Int)) %s)" (Id.to_string x) (fpl2smt2 y)
  | Pred(p, l) -> pred2smt2(p, l, [])


  (* (define-fun X2
    ( (v_0 Int) (v_1 Int) ) Bool
    (and (>= v_1 1) (>= (+ v_1 ( * (- 1) v_0)) 1))
  ) *)

let rec formula2smt2 fml = 
  match fml with
  | Formula.And fs -> Printf.sprintf "(and %s)" (List.map formula2smt2 fs |> String.concat " ")
  | Formula.Or fs -> Printf.sprintf "(or %s)" (List.map formula2smt2 fs |> String.concat " ")
  | Formula.Var _ -> assert false
  | Formula.Bool b -> begin
    match b with
    | true -> "true"
    | false -> "false"
  end
  | Formula.Pred(p, a, l) -> pred2smt2 (p, a, l)
  
(*  Rid.M.t *)
let pred_concrete_def ((name, (fml, args)) : (int * (('a, [`Int] Id.t, _) Hflmc2_syntax.Formula.gen_t * [`Int] Id.t list))) =
  let rec go args =
    match args with
    | arg::args -> ("(" ^ Id.to_string arg ^ " Int)") :: go args
    | [] -> []
  in
  Printf.sprintf "(define-fun %s ( %s ) Bool %s)\n"
    (Rid.to_string name)
    (go args |> String.concat " ")
    (formula2smt2 fml)