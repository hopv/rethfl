open Hflmc2_syntax
open Hflmc2_options
open Chc
open Rtype
open Smt2

type solver = [`Spacer | `Hoice | `Fptprove | `Eldarica | `Liu]

let fptprove_path_env = "fptprove"

type unsat_proof_node = 
  {
   id: int; 
   name: Rid.id; 
   args: int list; 
   nodes: int list }
type unsat_proof = unsat_proof_node list
  
let name_of_solver = function
  | `Spacer -> "spacer"
  | `Hoice -> "hoice"
  | `Fptprove -> "fptprove"
  | `Eldarica -> "eldarica"
  | `Liu      -> "liu"

let auto = `Auto(`Hoice, [])

let selected_solver is_tractable = 
  let sv = !Typing.solver in
  let solver =
    if sv = "auto" then auto
    else if sv = "z3" || sv = "spacer" then `Spacer
    else if sv = "hoice" then `Hoice
    else if sv = "fptprove" then `Fptprove
    else if sv = "liu" || sv = "hoice-haskell" || sv = "hoice-ex" then `Liu
    else if sv = "eldarica" || sv = "eld" then `Eldarica
    else failwith ("Unknown solver: " ^ sv)
  in
  if not is_tractable && solver != `Fptprove && solver != `Liu then
    `Fptprove
  else
    solver

(* set of template *)
let call_template cmd timeout = 
    let open Hflmc2_util in
    fun file -> 
    let _, out, _ = Fn.run_command ~timeout:timeout (Array.concat [cmd; [|file|]]) in
    lsplit2_fst out ~on:'\n'

let call_fptprove timeout file = 
  let open Hflmc2_util in
  let fptprove_path = 
    try Sys.getenv "fptprove" with
    | Not_found -> Filename.concat (Sys.getenv "HOME") "bitbucket.org/uhiro/fptprove"
  in
  let launch_script_path = Script.prepare_fptprove_script () in
  let _, out, _ = Fn.run_command ~timeout:timeout [|"bash"; launch_script_path; file; fptprove_path; string_of_int ((int_of_float timeout) + 5); !Hflmc2_options.pcsat_config|] in
  let l = String.split out ~on:',' in
  match List.nth l 1 with
    | Some(x) -> x, Some ""
    | None -> "Failed", None

let call_liu_solver timeout file =
  let open Hflmc2_util in
  let solver_path = 
    try Sys.getenv "liu_solver" with
    | Not_found -> failwith "Error: the environment variable \"liu_solver\" is not set" 
  in
  (* let _, out, _ = Fn.run_command ~timeout:timeout [|solver_path; "--preproc"; file|] in *)
  let _, out, _ = Fn.run_command ~timeout:timeout [|solver_path; file|] in
  let reg_time = Str.regexp "^solve time" in
  let reg_sat = Str.regexp "^Satisfied" in
  try (
    ignore @@ Str.search_forward reg_time out 0;
    try
      ignore @@ Str.search_forward reg_sat out 0;
      "sat", Some ""
    with
      | Not_found -> "unsat", None
  ) with
    | Not_found -> "Failed", None
  
let selected_cmd timeout = function
  | `Spacer -> call_template [|!Hflmc2_options.z3_path; "fp.engine=spacer"|] timeout
  | `Hoice -> call_template [|"hoice"; "--z3"; !Hflmc2_options.z3_path|] timeout
  | `Fptprove -> call_fptprove timeout  
  | `Eldarica -> call_template [|"eld"|] timeout
  | `Liu -> call_liu_solver timeout
  | _ -> failwith "you cannot use this"
  
let selected_cex_cmd = function
  | `Eldarica -> 
    [|"eld"; "-cex";  "-hsmt"|]
  | _ -> failwith "you cannot use this"

let prologue = "(declare-fun XX ( (List Int)) Bool)
"

let get_epilogue = 
  function 
  | `Spacer ->
    "\
    (check-sat-using (then propagate-values qe-light horn))
    (get-model)
    "
  | `Fptprove -> 
    "\
    (check-sat)
    "
  | `Hoice | `Liu ->
    "\
    (check-sat)
    (get-model)
    "
  | `Eldarica ->
    "\
    (check-sat)
    "

let rec collect_preds chcs m = 
  let rec inner rt m = match rt with 
  | RTemplate (p, l, ls) -> Rid.M.add p (List.length l, List.length ls) m
  | RAnd(x, y) | ROr(x, y) ->
    m |> inner x |> inner y
  | _ -> m
  in
  match chcs with
  | [] -> m
  | chc::chcs ->
    m |> inner chc.body |> inner chc.head |> collect_preds chcs

let collect_vars chc = 
  let collect_from_arith a m =
    let fvs = Arith.fvs a in
    List.fold_left IdSet.add m fvs
  in
  let rec collect_from_ariths ars m = match ars with
    | [] -> m
    | x::xs -> 
      m |> collect_from_arith x |> collect_from_ariths xs
  in
  let collect_from_ls_arith a m1 m2 =
    let (afvs, lfvs) = Arith.lfvs a in
    (List.fold_left IdSet.add m1 afvs, List.fold_left IdSet.add m2 lfvs)
  in
  let rec collect_from_ls_ariths ars m1 m2 = match ars with
    | [] -> (m1, m2)
    | x::xs ->
      let (set1, set2) = collect_from_ls_arith x m1 m2 in
      collect_from_ls_ariths xs set1 set2
  in
  let rec inner rt m1 m2 = match rt with
  | RTemplate(_, l, ls) -> 
    let avar1 = collect_from_ariths l m1 in
    let (avar2, lvar) = collect_from_ls_ariths ls m1 m2 in
    (IdSet.union avar1 avar2, lvar)
  | RPred(_, l) ->
    collect_from_ariths l m1, m2
  | RLsPred(_, ls) ->
    collect_from_ls_ariths ls m1 m2
  | RAnd(x, y) | ROr(x, y) ->
    let (m1, m2) = inner x m1 m2 in
    inner y m1 m2
  | _ -> (m1, m2)
  in
  let (m1, m2) = inner chc.head IdSet.empty IdSet.empty in
  inner chc.body m1 m2


let gen_assert solver chc =
  let (avars, lvars) = collect_vars chc in
  let vars_s = avars |> IdSet.to_list |> List.map var_def |> List.fold_left (^) "" in
  let lvars_s = lvars |> IdSet.to_list |> List.map lvar_def |> List.fold_left (^) "" in
  let vars_s = vars_s ^ lvars_s in
  let body = ref2smt2 chc.body in
  let head = ref2smt2 chc.head in
  let s = Printf.sprintf "(=> %s %s)" body head in
  if vars_s = "" && (solver == `Spacer || solver == `Fptprove || solver == `Eldarica || solver == `Liu) then
    Printf.sprintf "(assert %s)\n" s
  else
    Printf.sprintf "(assert (forall (%s) %s))\n" vars_s s  
  
let chc2smt2 env chcs solver = 
  let empty: (int * int) Rid.M.t = Rid.M.empty in
  let preds = collect_preds chcs empty in
  let preds =
    Rid.M.filter
      (fun id _ ->
        match Rid.M.find_opt id env with
        | Some _ -> false
        | None -> true
      )
      preds in
  let def = preds |> Rid.M.bindings |> List.map pred_def |> List.fold_left (^) "" in
  let concrete_def = env |> Rid.M.bindings |> List.map pred_concrete_def |> List.fold_left (^) "" in
  let body = chcs |> List.map (gen_assert solver) |> List.fold_left (^) "" in
  prologue ^ def ^ concrete_def ^ body ^ (get_epilogue solver)


let parse_model model = 
  let open Hflmc2_util in
  (* Ported from Iwayama san's parser 
     https://github.com/Hogeyama/hflmc2/blob/0c29b0b3a8aacb2496615244b3d93e98370c6eee/lib/refine/hornClauseSolver.ml#L215-L280
  *)
  let open Sexp in
  let fail f s = invalid_arg @@ f ^ ": " ^ Sexp.to_string s in
  let mk_var name =
     Id.{ name; id=0; ty=`Int }
  in
  let parse_arg = function
    | List [Atom v; Atom "Int" ] -> mk_var v
    | s -> fail "parse_arg" s
  in
  let rec parse_arith = function
    | Atom s ->
        begin match int_of_string s with
        | n -> Arith.mk_int n
        | exception _ -> Arith.mk_var' (mk_var s)
        end
    | List (Atom op :: ss) ->
        let op = match op with
          | "+" -> Arith.Add
          | "-" -> Arith.Sub
          | "*" -> Arith.Mult
          | s   -> fail "parse_arith:op" (Atom s)
        in
          begin
          match ss with
          | [] -> failwith "program error(parse_arith)"
          | [x] -> begin
              let e = 
              match op with 
              | Arith.Add | Arith.Sub -> 0
              | Arith.Mult | Arith.Div | Arith.Mod -> 1
              in
              Arith.mk_op op [Arith.Int(e); parse_arith x]
            end
          | _ -> 
            let [@warning "-8"] a::as' = List.map ss ~f:parse_arith in
              List.fold_left ~init:a as' ~f:begin fun a b ->
                Arith.mk_op op [a; b]
              end
            end
    | s -> fail "parse_arith" s
  in
  let rec parse_formula = function
    | Atom "true"  -> RTrue
    | Atom "false" -> RFalse
    | List (Atom a :: ss) ->
        let a = match a with
          | "="   -> `Pred Formula.Eq
          | "!="  -> `Pred Formula.Neq
          | "<="  -> `Pred Formula.Le
          | ">="  -> `Pred Formula.Ge
          | "<"   -> `Pred Formula.Lt
          | ">"   -> `Pred Formula.Gt
          | "and" -> `And 
          | "or"  -> `Or 
          | "not" -> `Not 
          | "exists" -> `Exists
          | s     -> fail "parse_formula:list" (Atom s)
        in
        begin match a with
        | `Pred pred ->
            RPred (pred, (List.map ~f:parse_arith ss))
        | `And ->
            let  [@warning "-8"] a::as' = List.map ss ~f:parse_formula in
            List.fold_left ~init:a as' ~f:(fun x y -> RAnd(x, y))
        | `Or -> 
            let  [@warning "-8"] a::as' = List.map ss ~f:parse_formula in
            List.fold_left ~init:a as' ~f:(fun x y -> ROr(x, y))
        | `Not -> 
            let [@warning "-8"] [f] = List.map ss ~f:parse_formula in
            negate_ref f
        | `Exists ->
          let [@warning "-8"] (List args)::[f] = ss in
          let as'' = List.map ~f:parse_arg args in
          let f = parse_formula f in
          let rec go a = match a with
            | [] -> f
            | x::xs -> RExists (x, go xs) in
          go as''
        end
    | s -> fail "parse_formula" s
  in
  let parse_def = function
    | List [Atom "define-fun"; Atom id; List args; Atom "Bool"; body] ->
        let args = List.map ~f:parse_arg args in
        let body = parse_formula body in
        let id = Rid.from_string id in
        (id, args, body)
    | s -> fail "parse_def" s
  in
  print_endline "Before model simplification:";
  print_endline model;
  let model = Simplify_model.simplify_model model in
  print_endline "After model simplification:";
  print_endline model;
  match Sexplib.Sexp.parse model with
  | Done(model, _) -> begin 
    match model with
    | List (Atom "model" :: sol) ->
        Ok(List.map ~f:parse_def sol)
    | _ -> Error "parse_model" 
    end
  | _ -> Error "failed to parse model"

let save_chc_to_smt2 env chcs solver = 
    let smt2 = chc2smt2 env chcs solver in
    let file = Hflmc2_util.gen_temp_filename ("/tmp/" ^ name_of_solver solver ^ "-") ".smt2" in
    let oc = open_out file in
    Printf.fprintf oc "%s" smt2;
    close_out oc;
    file

let check_sat ?(timeout=100000.0) env chcs solver = 
  let check_sat_inner timeout solver = 
    let file = save_chc_to_smt2 env chcs solver in
    let open Hflmc2_util in
    let f = selected_cmd timeout solver in
    match f file with
    | "unsat", _ -> `Unsat
    | "sat", Some model ->
      if Stdlib.String.trim model = "" then
        `Sat(Error "model was not produced")
      else begin
        let open Hflmc2_options in
        if !Typing.show_refinement then
          `Sat(parse_model model)
        else
          `Sat(Error "did not calculate refinement. Use --show-refinement")
      end
    | "unknown", Some _ -> `Unknown
    | _ -> (Printf.printf "Failed to handle the result of chc solver\n\n" ; `Fail)
  in 
  match solver with
  | `Auto(mainly, tries) ->
    let rec loop = function 
      | [] -> check_sat_inner timeout mainly
      | x::xs -> 
        begin
          let ret = check_sat_inner 1.0 x in
          match ret with
          | `Sat(_) | `Unsat -> ret
          | _ -> loop xs
        end
    in loop tries
  | `Eldarica | `Spacer | `Hoice | `Fptprove | `Liu as sv -> check_sat_inner timeout sv

(* usp: unsat proof *)
let rec unsat_proof_of_eldarica_cex nodes = 
  let open Eldarica in
  match nodes with
  | [] -> []
  | x::xs -> {id=Dag.(x.id); 
              name=if x.head="FALSE" then 
                Rid.false_id 
               else 
                Rid.from_string Dag.(x.head);
              args=Dag.(x.args);
              nodes=[];}::(unsat_proof_of_eldarica_cex xs) (* TODO *)
let get_unsat_proof ?(timeout=100.0) env chcs solver = 
  let open Hflmc2_util in
  let file = save_chc_to_smt2 env chcs solver in
  let cmd = selected_cex_cmd solver in
  let _, out, _ = Fn.run_command ~timeout:timeout (Array.concat [cmd; [|file|]]) in
  let p = Eldarica.parse_string out in
  unsat_proof_of_eldarica_cex p
