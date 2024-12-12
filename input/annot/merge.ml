let rec merge order l1 l2 =
  match l1,l2 with
      [],_ -> l2
    | _,[] -> l1
    | h1::t1, h2::t2 ->
      if order h1 h2 then h1 :: merge order t1 l2 else h2 :: merge order l1 t2

let rec length xs =
  match xs with
      [] -> 0
    | _::xs' -> 1 + length xs'

let rec make_list n =
  if n = 0
  then []
  else n :: make_list (n-1)

let order (x:int) y = x > y

let main n m =
  let xs = make_list n in
  let ys = make_list m in
    assert (length (merge order xs ys) = length xs + length ys)

