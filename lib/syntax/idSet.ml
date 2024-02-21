open Rethfl_util
include Set.Make'(Id.Key)
let singleton : 'a. 'a Id.t -> t =
  fun v -> singleton (Id.remove_ty v)
let remove : 'a. t -> 'a Id.t -> t =
  fun set x -> Set.remove set (Id.remove_ty x)
let mem set x = Set.mem set (Id.remove_ty x)
let add set x = Set.add set (Id.remove_ty x)
let union = Set.union
let filter = Set.filter
let to_list = Set.to_list
let choose = Set.choose
let diff = Set.diff
let elements = Set.elements
