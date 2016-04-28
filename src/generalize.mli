(** Generalize a concrete formula based on Paramecium to parameterized format
*)

open Paramecium

open Core.Std

(** Convert formula *)
val form_act : ?rename:bool -> formula -> paramdef list * paramref list * formula
