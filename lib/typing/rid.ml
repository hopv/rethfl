open Rethfl_syntax

type id = int

(* adhoc.. *)
let false_id = -1

let eq x y = x = y

(* This function is used by ppx-deriving eq *)
let equal_id = eq

let print_id = print_int

let to_string id = Printf.sprintf "X%d" id
let from_string s = Scanf.sscanf s "X%d" (fun x -> x) 

module M = Map.Make(Int)
