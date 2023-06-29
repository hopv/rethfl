(*
 * Assertion error
 *)

let rec loop (x:int) (i:int) =
  if i < 0 then
    x
  else if x < 1 then (* x <= 0*)
    loop (x - 1) (i - 1)
  else if x > 2 then (* x >= 3*)
    loop x (i - 1)
  else (* 1 2 *)
    loop (3 - x) (i - 1)

let main (n:int(*-:{v:Int | true}*)) =
  assert (loop (-3) n >= 3)