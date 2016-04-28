(** Check a formula with SMT solver
*)

exception Protocol_name_not_set

val set_context : string -> string -> bool

(** Judge if a given formula is satisfiable

    @param quiet true (default) to prevent to print output of smt solver to screen
    @param f the formula to be judged
    @return true if is satisfiable else false
*)
val is_satisfiable : ?quiet:bool -> string -> bool
