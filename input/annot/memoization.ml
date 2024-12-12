
let new_tbl (n:int) : (int*int) list = []
let get_tbl t (n:int) : int =
  let rec aux (ts:(int*int) list) =
    match ts with
        [] -> let rec loop u : int = loop () in loop ()
      | (k,x)::ts' -> if k=n then x else aux ts'
  in
    aux t
let mem_tbl t (n:int) =
  let rec aux (ts:(int*int) list) =
    match ts with
        [] -> false
      | (k,x)::ts' -> if k=n then true else aux ts'
  in
    aux t
let set_tbl t (n:int) (x:int) = (n,x)::t

let fib i =
  let rec f t0 n =
    if mem_tbl t0 n then
      (t0, get_tbl t0 n)
    else if n <= 2 then
      (t0, 1)
    else
      let (t1,r1) = f t0 (n-1) in
      let (t2,r2) = f t1 (n-2) in
      let r = r1 + r2 in
        (set_tbl t2 n r, r)
  in
  let _,r = f (new_tbl 17) i in
    assert (1 <= r && i-1 <= r)


