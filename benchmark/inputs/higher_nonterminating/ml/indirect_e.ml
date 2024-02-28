(* 途中にappを介してgを0になるまで再帰呼び出し。負値だと停止しない *)
let app f (x:int) (u:unit) = (f x u: unit)
let id (u:unit) = u
let rec g (x:int) =
  if x=0 then id else app g (x-1)
let main () =
  let t = read_int () in g t ()
