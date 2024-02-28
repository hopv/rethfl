open Core

let read_file file = In_channel.(with_file file ~f:input_all)

let save_file buf = 
  let file = Hflmc2_util.gen_temp_filename "/tmp/" ".smt2" in
  let oc = Stdlib.open_out file in
  Printf.fprintf oc "%s" buf;
  Stdlib.close_out oc;
  file

let fail f s = invalid_arg @@ f ^ ": " ^ Sexp.to_string s

let simplify_body acc args body =
  let open Sexp in
  let rec pargs args = match args with
    | (List [Atom v; Atom "Int" ])::args ->
      (List [Atom "declare-const"; Atom v; Atom "Int"])::(pargs args)
    | [] -> []
    | _ -> fail "pargs" (List args)
  in
  let args = pargs args |> List.map ~f:to_string |> String.concat ~sep:"\n"in
  let to_simplify = List [Atom "assert"; body] in
  (* Repeat application of ctx-solver-simplify may result in further simplificaion. *)
  let body = acc ^ "\n" ^ args ^ "\n" ^ (to_string to_simplify) ^ "\n(apply (then ctx-solver-simplify qe ctx-solver-simplify ctx-solver-simplify ctx-solver-simplify))" in
  let s = save_file body in
  (* print_endline @@ "file: " ^ s; *)
  let output_path = Hflmc2_util.gen_temp_filename "/tmp/" ".smt2" in
  (* these options prevent z3 from using "let" expressions *)
  let command = !Hflmc2_options.z3_path ^ " " ^ s ^ " pp.max_depth=10000 pp.min-alias-size=10000 > " ^ output_path in
  print_endline @@ "simplifing command: " ^ command;
  ignore @@ Unix.system command;
  let s = read_file output_path in
  match Sexplib.Sexp.parse s with
  | Done (model, _) -> begin
    match model with
    | List [Atom "goals"; List (Atom "goal"::xs)] -> begin
      let xs = List.filter ~f:(fun x -> match x with
        | Atom s -> begin
          match s with
          | "true" | "false" -> true
          | _ -> (* print_endline ("atom: " ^ s ^ ", skip"); *) false
        end
        | _ -> (* print_endline "not atom"; *) true
      ) xs in
      let body = 
        match xs with
        | [] -> Atom "true"
        | [x] -> x
        | xs -> List (Atom "and"::xs) in
      body
    end
    | _ -> fail "simplify_body" model
  end
  | _ -> invalid_arg "failed to parse model (2)" 

let simplify_model model =
  let open Sexp in
  let simplify_function_definition defs s = match s with
    | List [Atom "define-fun"; Atom id; List args; Atom "Bool"; body] ->
        let body = simplify_body defs args body in
        List [Atom "define-fun"; Atom id; List args; Atom "Bool"; body]
    | s -> fail "parse_def" s
  in
  (* print_string model; *)
  match Sexplib.Sexp.parse model with
  | Done(model, _) -> begin 
    match model with
    | List (Atom "model" :: sol) | List sol -> begin
      let r = 
        List.fold_left
          sol
          ~f:(fun acc d ->
            acc ^ "\n  " ^ (simplify_function_definition acc d |> to_string)
          )
          ~init:"  " in
      "(model\n  " ^ (Stdlib.String.trim r) ^ "\n)"
    end
    | _ -> invalid_arg "model syntax error: parse_model" 
    end
  | _ -> invalid_arg "failed to parse model"
