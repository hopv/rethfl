
(* バグっとる *)
(*
let rec is_true : Hfl.t -> bool =
  fun phi -> match phi with
  | Bool b -> b
  | And(phi1, phi2, _) -> is_true phi1 && is_true phi2
  | Or (phi1, phi2, _) -> is_true phi1 || is_true phi2
  | _ -> false
let rec is_false : Hfl.t -> bool =
  fun phi -> match phi with
  | Bool b -> not b
  | And(phi1, phi2, _) -> is_false phi1 || is_false phi2
  | Or (phi1, phi2, _) -> is_false phi1 && is_false phi2
  | _ -> false

let rec hfl : ?force:bool -> Hfl.t -> Hfl.t =
  fun ?(force=false) phi ->
    match Subst.Hfl.reduce phi with
    | And(phi1, phi2, k) when k = `Inserted || force ->
        let phi1 = hfl ~force phi1 in
        let phi2 = hfl ~force phi2 in
        begin match () with
        | _ when is_true  phi2 -> phi1
        | _ when is_true  phi1 -> phi2
        | _ when is_false phi2 -> Bool false
        | _ when is_false phi1 -> Bool false
        | _                    -> And(phi1, phi2, k)
        end
    | Or(phi1, phi2, k) when k = `Inserted || force ->
        let phi1 = hfl ~force phi1 in
        let phi2 = hfl ~force phi2 in
        begin match () with
        | _ when is_false phi2 -> phi1
        | _ when is_false phi1 -> phi2
        | _ when is_true  phi2 -> Bool true
        | _ when is_true  phi1 -> Bool true
        | _ -> Or(phi1, phi2, k)
        end
    | And(phi1, phi2, k) -> (* preserve the structure *)
        let phi1 = hfl ~force phi1 in
        let phi2 = hfl ~force phi2 in
        begin match () with
        | _ when is_false phi1 -> And(Bool false, Bool true, k)
        | _ when is_false phi2 -> And(Bool true, Bool false, k)
        | _                    -> And(phi1, phi2, k)
        end
    | Or(phi1, phi2, k) -> (* preserve the structure *)
        let phi1 = hfl ~force phi1 in
        let phi2 = hfl ~force phi2 in
        begin match () with
        | _ when is_true phi1 -> Or(Bool true, Bool false, k)
        | _ when is_true phi2 -> Or(Bool false, Bool true, k)
        | _                   -> Or(phi1, phi2, k)
        end
    | Exists(l,phi)  -> Exists(l, hfl ~force phi)
    | Forall(l,phi)  -> Forall(l, hfl ~force phi)
    | Fix(x,phi,z)   -> Fix(x, hfl ~force phi, z)
    | Abs(x,phi)     -> Abs(x, hfl ~force phi)
    | App(phi1,phi2) -> App(hfl ~force phi1, hfl ~force phi2)
    | phi -> phi
*)

let rec hfl : ?force:bool -> Hfl.t -> Hfl.t =
  fun ?(force=false) phi ->
    match Subst.Hfl.reduce phi with
    (* | And(phi1, phi2, k) when k = `Inserted || force -> *)
    (*     begin match hfl ~force phi1, hfl ~force phi2 with *)
    (*     | phi1, Bool true -> phi1 *)
    (*     | Bool true, phi2 -> phi2 *)
    (*     | Bool false, _   -> Bool false *)
    (*     | _, Bool false   -> Bool false *)
    (*     | phi1, phi2      -> And(phi1, phi2, k) *)
    (*     end *)
    (* | Or(phi1, phi2, k) when k = `Inserted || force -> *)
    (*     begin match hfl ~force phi1, hfl ~force phi2 with *)
    (*     | phi1, Bool false -> phi1 *)
    (*     | Bool false, phi2 -> phi2 *)
    (*     | Bool true, _     -> Bool true *)
    (*     | _, Bool true     -> Bool true *)
    (*     | phi1, phi2       -> Or(phi1, phi2, k) *)
    (*     end *)
    (* | And(phi1, phi2, k) -> *)
    (*     begin match hfl ~force phi1, hfl ~force phi2 with *)
    (*     | Bool false, _ -> And(Bool false, Bool true, k) *)
    (*     | _, Bool false -> And(Bool true, Bool false, k) *)
    (*     | phi1, phi2    -> And(phi1, phi2, k) *)
    (*     end *)
    (* | Or(phi1, phi2, k) -> *)
    (*     begin match hfl ~force phi1, hfl ~force phi2 with *)
    (*     | Bool true, _     -> Or(Bool true, Bool false, k) *)
    (*     | _, Bool true     -> Or(Bool false, Bool true, k) *)
    (*     | phi1, phi2       -> Or(phi1, phi2, k) *)
    (*     end *)
    (* | Exists(l,phi)  -> Exists(l, hfl ~force phi) *)
    (* | Forall(l,phi)  -> Forall(l, hfl ~force phi) *)
    (* | Fix(x,phi,z)   -> Fix(x, hfl ~force phi, z) *)
    (* | Abs(x,phi)     -> Abs(x, hfl ~force phi) *)
    (* | App(phi1,phi2) -> App(hfl ~force phi1, hfl ~force phi2) *)
    | phi -> phi
(* let hfl : ?force:bool -> Hfl.t -> Hfl.t = *)
(*   fun ?(force=false) x -> x *)
