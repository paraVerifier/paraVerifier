(** Check a invariant with NuSMV
*)

(* Raises when there are some errors in the NuSMV code *)
exception Protocol_name_not_set

val set_context : ?escape:(string -> string) -> ?smv_ord:string -> string -> string -> int

(** Judge if a given invariant is true invariant

    @param quiet true (default) to prevent to print output of smt solver to screen
    @param inv the inv to be judged
    @return true if is true invariant else false
*)
val is_inv : ?quiet:bool -> string -> bool

