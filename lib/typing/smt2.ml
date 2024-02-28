open Hflmc2_syntax
open Rtype
open Fpl

let rec gen_len_args len = 
  if len < 1 then ""
  else if len = 1 then "Int"
  else "Int " ^ gen_len_args (len - 1)

let rec gen_len_ls_args len = 
  if len < 1 then ""
  else if len = 1 then "(List Int)"
  else "(List Int) " ^ gen_len_ls_args (len - 1)

let pred_def (name, (len1, len2)) =
  gen_len_args len1 ^ " " ^ gen_len_ls_args len2 |> Printf.sprintf "(declare-fun %s (%s) Bool)\n" (Rid.to_string name)


let var_def id = id |> Id.to_string |> Printf.sprintf "(%s Int)"
let lvar_def id = id |> Id.to_string |> Printf.sprintf "(%s (List Int))"

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
  end args

let lspred2smt2 pred args = 
  let open Formula in
  Printf.sprintf 
  begin
    match pred with
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
and ariths2smt2 l =
    l |> List.map arith2smt2 |> List.fold_left (fun s x -> s ^ " " ^ x) "" 

let rec lsarith2smt2 = 
  let open Arith in
  function 
  | Nil -> Printf.sprintf "nil"
  | LVar id -> Id.to_string id
  | Cons(hd, tl) -> 
    let head = arith2smt2 hd in
    let tail = lsarith2smt2 tl in
    Printf.sprintf "(insert %s %s)" head tail
and lsariths2smt2 l =
    l |> List.map lsarith2smt2 |> List.fold_left (fun s x -> s ^ " " ^ x) "" 
let template2smt2 (p, l, ls) =
  let name = Rid.to_string p in
  let args = ariths2smt2 l in
  let lsargs = lsariths2smt2 ls in
    if args = "" && lsargs = "" then
      Printf.sprintf "%s" name 
    else
      Printf.sprintf "(%s %s %s)" name args lsargs

let pred2smt2 (p, l) =
  let args = ariths2smt2 l in
  pred2smt2 p args

let lspred2smt2 (p, l) =
  let args = lsariths2smt2 l in
  lspred2smt2 p args

let rec ref2smt2 rt = match rt with
  | RTrue -> "true"
  | RFalse -> "false"
  | RAnd(x, y) -> Printf.sprintf "(and %s %s)" (ref2smt2 x) (ref2smt2 y)
  | ROr(x, y) -> Printf.sprintf "(or %s %s)" (ref2smt2 x) (ref2smt2 y)
  | RTemplate(p, l, ls) -> template2smt2 (p, l, ls)
  | RPred(p, l) -> pred2smt2(p, l)
  | RLsPred(p, l) -> lspred2smt2(p, l)
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
  | Pred(p, l) -> pred2smt2(p, l)


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
  | Formula.Pred (p, l) -> pred2smt2 (p, l)
  | Formula.LsPred(p, l) -> lspred2smt2 (p, l)
  
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