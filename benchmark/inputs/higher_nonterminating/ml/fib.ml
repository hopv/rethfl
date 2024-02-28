(* 
let rec fib n =
  if n = 0 || n = 1 then 1
  else
    fib (n - 1) + fib (n - 2)

let () = 
  List.iter (fun n ->
    print_endline @@ string_of_int @@ fib n
  ) [0;1;2;3;4;5;6;7;8;9;10]
   *)

let rec fib_CPS_nonterm n k =
  if n = 0 || n = 1 then k 1
  else
    let pn = n - 1 in
    let ppn = n - 2 in
    fib_CPS_nonterm pn (fun a ->
      fib_CPS_nonterm ppn (fun b ->
        k (a + b)))

let id (n:int) = n
let main () =
  let r = read_int () in
  if r <= (-3) then
    fib_CPS_nonterm (-3) id
  else if r <= 0 then
    fib_CPS_nonterm 0 id
  else if r <= 1 then
    fib_CPS_nonterm 1 id
  else if r <= 3 then
    fib_CPS_nonterm 3 id
  else
    fib_CPS_nonterm 10 id


let () = print_endline @@ string_of_int @@ main ()
