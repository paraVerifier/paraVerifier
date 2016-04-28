(** The most fundamental language for this tool
*)

open Core.Std

(*------------------------------ Types ---------------------------------*)

(** Constants *)
type const =
  | Intc of int
  | Strc of string
  | Boolc of bool
with sexp

val intc : int -> const
val strc : string -> const
val boolc : bool -> const

(** Basic types available, including integers and enumerations.
    Types are defined by their names and range.
*)
type typedef =
  | Enum of string * const list
with sexp

val enum : string -> const list -> typedef

(** Parameter definitions
    + paramdef, name and typename
*)
type paramdef =
  | Paramdef of string * string
with sexp

val paramdef : string -> string -> paramdef

(** Parameter references
    + Paramref, var name
    + Paramfix, var name, typename, value
*)
type paramref =
  | Paramref of string
  | Paramfix of string * string * const
with sexp

val paramref : string -> paramref
val paramfix : string -> string -> const -> paramref

(** Variable definitions, each with its name and name of its type
    + Array var: name, param definitions, type name
*)
type vardef =
  | Arrdef of (string * paramdef list) list * string
with sexp

val arrdef : (string * paramdef list) list -> string -> vardef

(** Variable reference *)
type var =
  | Arr of (string * paramref list) list
with sexp

val arr : (string * paramref list) list -> var

(** Represents expressions, including
    + Constants
    + Variable references
    + Parameter
    + Ite exp
*)
type exp =
  | Const of const
  | Var of var
  | Param of paramref
  | Ite of formula * exp * exp
(** Boolean expressions, including
    + Boolean constants, Chaos as True, Miracle as false
    + Equation expression
    + Other basic logical operations, including negation,
      conjuction, disjuction, and implication
*)
and formula =
  | Chaos
  | Miracle
  | Eqn of exp * exp
  | Neg of formula
  | AndList of formula list
  | OrList of formula list
  | Imply of formula * formula
with sexp

val const : const -> exp
val var : var -> exp
val param : paramref -> exp
val ite : formula -> exp -> exp -> exp

val chaos : formula
val miracle : formula
val eqn : exp -> exp -> formula
val neg : formula -> formula
val andList : formula list -> formula
val orList : formula list -> formula
val imply : formula -> formula -> formula

(** Assignment statements, including
    + Single assignment
    + Parallel assignment
*)
type statement =
  | Assign of var * exp
  | Parallel of statement list
with sexp

val assign : var -> exp -> statement
val parallel : statement list -> statement

(** Represents rules which consists of guard and assignments
    + Rule: name, parameters, guard, assignments
*)
type rule = 
  | Rule of string * paramdef list * formula * statement
with sexp

val rule : string -> paramdef list -> formula -> statement -> rule

(** Represents properties
    + Prop: name, parameters, formula
*)
type prop =
  | Prop of string * paramdef list * formula
with sexp

val prop : string -> paramdef list -> formula -> prop

(** Represents the whole protocol *)
type protocol = {
  name: string;
  types: typedef list;
  vardefs: vardef list;
  init: statement;
  rules: rule list;
  properties: prop list;
}
with sexp

(*----------------------------- Exceptions ----------------------------------*)

(** The actual parameters can't match with their definitions *)
exception Unmatched_parameters

(** Unexhausted instantiation
    This exception should never be raised. Once raised, There should be a bug in this tool.
*)
exception Unexhausted_inst

(*----------------------------- Functions ----------------------------------*)

(** Convert a int list to const list *)
val int_consts : int list -> const list
(** Convert a string list to const list *)
val str_consts : string list -> const list
(** Convert a boolean list to const list *)
val bool_consts : bool list -> const list

(** Find the values range of a type by its name *)
val name2type : tname:string -> types:typedef list -> const list

(* Generate Cartesian production of all possible values of a `paramdef` set
    Each value in each set is index name with its associated paramfix
    Result is like [
      [Paramfix("x", "bool", Boolc true); Paramfix("n", "int", Intc 1)]; 
      [Paramfix("x", "bool", Boolc false); Paramfix("n", "int", Intc 1)]
    ]
*)
val cart_product_with_paramfix : paramdef list -> typedef list -> paramref list list

(** Get the name of parameter
    e.g., For parameter Paramfix("x", "bool", Boolc true)), generate "x"
    For parameter Paramref("n"), generate "n"
*)
val name_of_param : paramref -> string

val set_param_name : paramref -> string -> paramref

val typename_of_paramfix : paramref -> string

val find_paramfix : paramref list -> string -> paramref option

val find_paramdef : paramdef list -> string -> paramdef option



(** attach consts i to string name *)
val attach_list : string -> const list -> string

(** Apply a paramref with param, i.e., cast it to consts *)
val apply_paramref : paramref -> p:paramref list -> paramref

(** Apply array with param *)
val apply_array : var -> p:paramref list -> var

(** Apply exp with param *)
val apply_exp : exp -> p:paramref list -> exp

(** Apply formula with param *)
val apply_form : formula -> p:paramref list -> formula

(** Apply statement with param *)
val apply_statement : statement -> p:paramref list -> statement

(** Apply rule with param *)
val apply_rule : rule -> p:paramref list -> rule

(** Apply property with param *)
val apply_prop : prop -> p:paramref list -> prop







(*********************************** Module Variable Names **************************************)

(** Get variable names in the components *)
module VarNames : sig

  (** Names of var *)
  val of_var : var -> String.Set.t

  (** Names of exp *)
  val of_exp : exp -> String.Set.t

  (** Names of formula *)
  val of_form : formula -> String.Set.t

  val of_statement : statement -> String.Set.t

  val of_rule : rule -> String.Set.t
end




module VarNamesOfAssigns : sig
  val of_statement : statement -> String.Set.t
  val of_rule : rule -> String.Set.t
end





(*********************************** Module Variable Names, with Param values *****************)

(** Get variable names in the components *)
module VarNamesWithParam : sig

  val of_exp : of_var:(var -> String.Set.t) -> exp -> String.Set.t
  val of_form : of_var:(var -> String.Set.t) -> formula -> String.Set.t
  val of_statement : of_var:(var -> String.Set.t) -> statement -> String.Set.t
  val of_rule : of_var:(var -> String.Set.t) -> rule -> String.Set.t

end
