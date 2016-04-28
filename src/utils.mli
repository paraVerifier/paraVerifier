(** This library provides some useful functions
*)

(*----------------------------- Switches ----------------------------------*)

val debug_switch : bool ref

(*----------------------------- Exceptions ----------------------------------*)

(* This exception is for stop warnings. It will never be raised. *)
exception Empty_exception

(** Exception raised when could not find something *)
exception Cannot_find of string

(*----------------------------- Functions ----------------------------------*)

val up_to : int -> int list

(** Generate the permutation of a list *)
val permutation : 'a list -> 'a list list

(** Generate the combination of a list *)
val combination : 'a list -> int -> 'a list list

(** Generate all combinations of a list *)
val combination_all : 'a list -> 'a list list

(** Combination firstly and permutation for each element of the combination *)
val combination_permutation : 'a list -> int -> 'a list list

(** Generate Cartesian Production of a set of lists
    For example, given [[1;2]; [1;3]] produces [[1;1]; [1;3]; [2;1]; [2;3]]

    @param list the given set of lists, whose elements will be omitted if it is []
    @return the generated Cartesian Production
*)
val cartesian_product : 'a list list -> 'a list list

(** Judge if all elements in list satisfy function f

    @param the list
    @param f a function maps elements in list to bool
    @return true if satisfy else false
*)
val all : 'a list -> f:('a -> bool) -> bool

(** Judge if any elements in list satisfies function f

    @param the list
    @param f a function maps elements in list to bool
    @return true if satisfies else false
*)
val any : 'a list -> f:('a -> bool) -> bool

(** Reduce a list, if the list is empty, a default value is returned *)
val reduce: 'a list -> default:'a -> f:('a -> 'a -> 'a) -> 'a

val rm_from_list : 'a list -> f:('a -> bool) -> 'a list

(** Partition a list to a set of labeled lists, with function f
    e.g., for list [1;2;3;4;5;6] and function (fun x -> x mod 3),
    generate list [(1, [1;4]); (2, [2;5]); (0, [3;6])]
*)
val partition_with_label : 'a list -> f:('a -> 'b) -> ('b * 'a list) list

(** Partition a list to a set of lists, with function f
    e.g., for list [1;2;3;4;5;6] and function (fun x -> x mod 3),
    generate list [[1;4]; [2;5]; [3;6]]
*)
val partition : 'a list -> f:('a -> 'b) -> 'a list list

val stupid_dedup_list : 'a list -> f:('a -> 'a -> bool) -> 'a list

val string_replace : string -> string -> string -> string


(** Denotes there are errors while execute a program *)
exception Exec_error

(** Execute a program with some arguments then fetch the output.
    This function will block the main process.

    @param prog the program to be executed
    @param args arguments
    @return stdout string
*)
val exec : prog:string -> args:string list -> string * string

(** Execute a program with some arguments and some input strings then fetch the output.
    This function will block the main process.

    @param prog the program to be executed
    @param args arguments
    @param input input string
    @return stdout string
*)
val exec_with_input : prog:string -> args:string list -> string -> string * string

(** Some usefule colorful print functions *)
module Prt : sig

  (** Wrong color value *)
  exception Wrong_color

  (** Basic color *)
  type basic_color =
    | Black
    | Red
    | Green
    | Yellow
    | Blue
    | Magenta
    | Cyan
    | White

  (** More color
      + Basic basic color
      + Bold bold color
      + RGB 6x6x6 color cube
      + Gray 24 grayscale levels
  *)
  type color

  val basic : basic_color -> color
  val bold : basic_color -> color
  val rgb : int -> int -> int -> color
  val gray : int -> color

  (** Print colorful text on terminal

      @param text string to be printed
      @param color color of string
  *)
  val colorful : text:string -> color:color -> unit

  (** Print info string *)
  val info : string -> unit

  (** Print warning string *)
  val warning : string -> unit

  (** Print error string *)
  val error : string -> unit

end
