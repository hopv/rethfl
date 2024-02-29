let () =
  let file =
    match Rethfl.Options.parse() with
    | Some (`File file) -> file
    | Some `Stdin ->
        let tmp_file = Filename.temp_file "stdin-" ".in" in
        let contents = Hflmc2_util.In_channel.(input_all stdin) in
        Hflmc2_util.Out_channel.with_file tmp_file ~f:begin fun ch ->
          Hflmc2_util.Out_channel.output_string ch contents
        end;
        tmp_file
    | None -> exit 1
  in
    begin match Rethfl.main file with
    | r ->
        Fmt.pr "@[<v 2>Verification Result:@,%s@]@." @@ Rethfl.show_result r;
        if Logs.Src.level Rethfl.log_src <> None
          then Rethfl.report_times()
    | exception
        ( Rethfl.Util.Fn.Fatal e
        | Rethfl.Syntax.ParseError e
        | Rethfl.Syntax.LexingError e
        ) -> print_endline e; exit 1
    end;
