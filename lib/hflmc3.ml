module Util        = Hflmc2_util
module Options     = Hflmc2_options
module Syntax      = Hflmc2_syntax
module Typing      = Hflmc2_typing
module Eldarica    = Eldarica

open Util
open Syntax

let log_src = Logs.Src.create "Main"
module Log = (val Logs.src_log @@ log_src)

type result = [ `Valid | `Invalid | `Unknown | `Fail]

let show_result = function
  | `Valid      -> "Valid"
  | `Invalid    -> "Invalid"
  | `Unknown    -> "Unknown"
  | `Fail       -> "Fail"

let show_tractability = Typing.Infer.show_tractability

let measure_time f =
  let start  = Unix.gettimeofday () in
  let result = f () in
  let stop   = Unix.gettimeofday () in
  result, stop -. start

let times = Hashtbl.create (module String)
let add_mesure_time tag f =
  let r, time = measure_time f in
  let if_found t = Hashtbl.set times ~key:tag ~data:(t+.time) in
  let if_not_found _ = Hashtbl.set times ~key:tag ~data:time in
  Hashtbl.find_and_call times tag ~if_found ~if_not_found;
  r
let all_start = Unix.gettimeofday ()
let report_times () =
  let total = Unix.gettimeofday() -. all_start in
  let kvs = Hashtbl.to_alist times @ [("total", total)] in
  match List.max_elt ~compare (List.map kvs ~f:(String.length<<<fst)) with
  | None -> Print.pr "no time records"
  | Some max_len ->
      Print.pr "Profiling:@.";
      List.iter kvs ~f:begin fun (k,v) ->
        let s =
          let pudding = String.(init (max_len - length k) ~f:(Fn.const ' ')) in
          "  " ^ k ^ ":" ^ pudding
        in Print.pr "%s %f sec@." s v
      end

let remove_disjunctions psi top =
  let (top, psi) = Typing.Remove_disjunctions.convert (Var top, psi) in
  let psi = {
    Hflz.var=
      (let id = Id.gen_id () in
      {Id.id = id; name = "X" ^ string_of_int id; ty=(Type.TyBool ())});
    body=top;
    fix=Fixpoint.Greatest
  }::psi in
  let psi = Syntax.Trans.Simplify.hflz_hes psi in
  Syntax.Trans.Preprocess.main psi
  |> (fun (psi, top) ->
    match top with
    | Some top -> (psi, top)
    | None -> assert false
  )
(* alrm hup int term usr1 usr2 *)
let set_signals () =
  let f =
    Sys.Signal_handle
      (fun code ->
        print_endline @@ "signal code: " ^ string_of_int code;
        Hflmc2_util.remove_generated_files ();
        Sys.set_signal code Sys.Signal_default;
        Unix.kill (Unix.getpid ()) code
        ) in
  Sys.set_signal Sys.sigalrm f;
  Sys.set_signal Sys.sighup f;
  Sys.set_signal Sys.sigint f;
  Sys.set_signal Sys.sigterm f;
  Sys.set_signal Sys.sigusr1 f;
  Sys.set_signal Sys.sigusr2 f

let main file =
  if !Hflmc2_options.remove_temporary_files then set_signals ();
  Log.app begin fun m -> m ~header:"z3 path" "%s" !Hflmc2_options.z3_path end;
  let psi, anno_env = Syntax.parse_file file in
  let anno_env =
    if !Options.use_annotation then
      anno_env
    else IdMap.empty in
  Log.app begin fun m -> m ~header:"Input" "%a"
    Print.(hflz_hes simple_ty_) psi
  end;
  let psi = Syntax.Trans.Simplify.hflz_hes psi in
  Log.app begin fun m -> m ~header:"Simplified" "%a"
    Print.(hflz_hes simple_ty_) psi
  end;
  let psi, top = Syntax.Trans.Preprocess.main psi in
  let result =
    match top with
    | Some(top) -> begin
      let psi, top =
        if !Hflmc2_options.remove_disjunctions
          then (remove_disjunctions psi top)
          else (psi, top) in
      try (
        match Typing.main anno_env psi top with
        | `Sat ->  `Valid
        | `Unsat ->  `Invalid
        | `Unknown -> `Unknown
        | _ -> `Fail
      ) with Typing.Infer.ExnIntractable -> (
        if !Hflmc2_options.remove_disjunctions_if_intractable then (
          Hflmc2_options.stop_if_tractable := false;
          let psi, top = remove_disjunctions psi top in
          match Typing.main anno_env psi top with
          | `Sat ->  `Valid
          | `Unsat ->  `Invalid
          | `Unknown -> `Unknown
          | _ -> `Fail
        ) else raise Typing.Infer.ExnIntractable
      )
    end
    | None -> print_string "[Warn]input was empty\n";
        `Valid (* because the input is empty *)
  in
  if !Hflmc2_options.remove_temporary_files then Hflmc2_util.remove_generated_files ();
  result
  