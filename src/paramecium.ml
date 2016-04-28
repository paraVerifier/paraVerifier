(** The most fundamental language for this tool
*)

open Utils

open Core.Std

(*------------------------------ Types ---------------------------------*)

(** Constants *)
type const =
  | Intc of int
  | Strc of string
  | Boolc of bool
with sexp

let intc i = Intc i
let strc s = Strc s
let boolc b = Boolc b

(** Basic types available, including integers and enumerations.
    Types are defined by their names and range.
*)
type typedef =
  | Enum of string * const list
with sexp

let enum name letues = Enum(name, letues)

(** Parameter definitions
    + Paramdef, name and typename
*)
type paramdef =
  | Paramdef of string * string
with sexp

let paramdef name typename = Paramdef(name, typename)

(** Parameter references
    + Paramref, var name
    + Paramfix, var name, typename, value
*)
type paramref =
  | Paramref of string
  | Paramfix of string * string * const
with sexp

let paramref name = Paramref name
let paramfix vname tname value = Paramfix (vname, tname, value)

(** Variable definitions, each with its name and name of its type
    + Array var: name, param definitions, type name
*)
type vardef =
  | Arrdef of (string * paramdef list) list * string
with sexp

let arrdef ls typename = Arrdef(ls, typename)

(** Variable reference *)
type var =
  | Arr of (string * paramref list) list
with sexp

let arr ls = Arr(ls)

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

let const c = Const c
let var v = Var v
let param paramref = Param(paramref)
let ite f e1 e2 = Ite(f, e1, e2)

let chaos = Chaos
let miracle = Miracle
let eqn e1 e2 = Eqn(e1, e2)
let neg f = Neg f
let andList fs = AndList fs
let orList fs = OrList fs
let imply f1 f2 = Imply(f1, f2)

(** Assignment statements, including
    + Single assignment
    + Parallel assignment
*)
type statement =
  | Assign of var * exp
  | Parallel of statement list
with sexp

let assign v e = Assign(v, e)
let parallel statements = Parallel statements

(** Represents rules which consists of guard and assignments
    + Rule: name, parameters, guard, assignments
*)
type rule = 
  | Rule of string * paramdef list * formula * statement
with sexp

let rule name paramdef f s = Rule(name, paramdef, f, s)

(** Represents properties
    + Prop: name, parameters, formula
*)
type prop =
  | Prop of string * paramdef list * formula
with sexp

let prop name paramdef f = Prop(name, paramdef, f)

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
let int_consts ints = List.map ints ~f:intc
(** Convert a string list to const list *)
let str_consts strs = List.map strs ~f:strc
(** Convert a boolean list to const list *)
let bool_consts bools = List.map bools ~f:boolc

(** Find the letues range of a type by its name
*)
let name2type ~tname ~types =
  let op_t = List.find types ~f:(fun (Enum(n, _)) -> n = tname) in
  match op_t with
  | None -> raise (Cannot_find (sprintf "type %s" tname))
  | Some (Enum(_, consts)) -> consts

(* Generate Cartesian production of all possible values of a `paramdef` set
    Result is like [[Boolc true; Intc 1]; [Boolc false; Intc 1]]
*)
let cart_product paramdefs types =
  paramdefs
  |> List.map ~f:(fun (Paramdef(_, tname)) -> name2type ~tname ~types)
  |> cartesian_product

(* Generate Cartesian production of all possible values of a `paramdef` set
    Each value in each set with its index name
    Result is like [[("x", Boolc true); ("n", Intc 1)]; [("x", Boolc false); ("n", Intc 1)]]
*)
let cart_product_with_name paramdefs types =
  paramdefs
  |> List.map ~f:(fun (Paramdef(n, tname)) -> (n, name2type ~tname ~types))
  |> List.map ~f:(fun (n, t) -> List.map t ~f:(fun x -> (n, x)))
  |> cartesian_product

(* Generate Cartesian production of all possible values of a `paramdef` set
    Each value in each set is index name with its associated paramfix
    Result is like [
      [Paramfix("x", "bool", Boolc true); Paramfix("n", "int", Intc 1)]; 
      [Paramfix("x", "bool", Boolc false); Paramfix("n", "int", Intc 1)]
    ]
*)
let cart_product_with_paramfix paramdefs types =
  paramdefs
  |> List.map ~f:(fun (Paramdef(n, tname)) -> (n, (tname, name2type ~tname ~types)))
  |> List.map ~f:(fun (n, (tname, trange)) -> List.map trange ~f:(fun x -> paramfix n tname x))
  |> cartesian_product

(** Get the name of parameter
    e.g., For parameter Paramfix("x", "bool", Boolc true)), generate "x"
    For parameter Paramref("n"), generate "n"
*)
let name_of_param pr =
  match pr with
  | Paramref(n)
  | Paramfix(n, _, _) -> n

let set_param_name pr name =
  match pr with
  | Paramref(_) -> paramref name
  | Paramfix(_, tn, c) -> paramfix name tn c

let typename_of_paramfix pf =
  match pf with
  | Paramref(_) -> raise Unexhausted_inst
  | Paramfix(_, tn, _) -> tn

let find_paramfix pfs name =
  List.find pfs ~f:(fun pr -> name = (name_of_param pr))

let find_paramdef pds name =
  List.find pds ~f:(fun (Paramdef(n, _)) -> name = n)






(* attach const i to string name *)
let attach name i =
  match i with
  | Strc(x) -> sprintf "%s[%s]" name x
  | Intc(x) -> sprintf "%s[%d]" name x
  | Boolc(x) -> sprintf "%s[%b]" name x

(** attach consts i to string name *)
let attach_list name i_list =
  List.fold i_list ~init:name ~f:attach

(** Apply a paramref with param, i.e., cast it to consts *)
let apply_paramref pr ~p =
  match pr with
  | Paramref(s) -> (
      match find_paramfix p s with
      | None -> pr (* raise (Cannot_find (sprintf "parameter reference for %s" s)) *)
      | Some pf -> pf
    )
  | Paramfix(_) -> pr

(** Apply array with param *)
let apply_array (Arr(ls)) ~p =
  arr (List.map ls ~f:(fun (name, params) ->
    name, List.map params ~f:(apply_paramref ~p)
  ))

(** Apply exp with param *)
let rec apply_exp exp ~p =
  match exp with
  | Var(x) -> var (apply_array x ~p)
  | Param(pr) -> param (apply_paramref pr ~p)
  | Const(_) -> exp
  | Ite(f, e1, e2) -> ite (apply_form f ~p) (apply_exp e1 ~p) (apply_exp e2 ~p)
(** Apply formula with param *)
and apply_form f ~p =
  match f with
  | Chaos
  | Miracle -> f
  | Eqn(e1, e2) -> eqn (apply_exp e1 ~p) (apply_exp e2 ~p)
  | Neg(form) -> neg (apply_form form ~p)
  | AndList(fl) -> andList (List.map fl ~f:(apply_form ~p))
  | OrList(fl) -> orList (List.map fl ~f:(apply_form ~p))
  | Imply(f1, f2) -> imply (apply_form f1 ~p) (apply_form f2 ~p)

(** Apply statement with param *)
let rec apply_statement statement ~p =
  match statement with
  | Assign(v, e) -> assign (apply_array v ~p) (apply_exp e ~p)
  | Parallel(sl) -> parallel (List.map sl ~f:(apply_statement ~p))

(* Check if a given parameter matches with the paramdef *)
let name_match params defs =
  if List.length params = List.length defs then
    let same_name pr (Paramdef(n2, _)) = (name_of_param pr) = n2 in
    List.map2_exn params defs ~f:same_name
    |> List.fold ~init:true ~f:(fun res x -> res && x)
  else
    false

(** Apply rule with param *)
let apply_rule r ~p =
  let Rule(n, paramdefs, f, s) = r in
  let name =
    if p = [] then n
    else begin
      let const_act c =
        match c with
        | Intc(i) -> Int.to_string i
        | Strc(s) -> String.lowercase s
        | Boolc(b) -> String.uppercase (Bool.to_string b)
      in
      let paramref_act pr =
        match pr with
        | Paramfix(_, _, c) -> sprintf "[%s]" (const_act c)
        | Paramref(_) -> raise Unexhausted_inst
      in
      sprintf "%s%s" n (String.concat (List.map p ~f:paramref_act))
    end
  in
  if name_match p paramdefs then
    rule name [] (apply_form f ~p) (apply_statement s ~p)
  else
    raise Unmatched_parameters

(** Apply property with param *)
let apply_prop property ~p =
  let Prop(name, paramdefs, f) = property in
  if name_match p paramdefs then
    prop name [] (apply_form f ~p)
  else
    raise Unmatched_parameters










(*********************************** Module Variable Names **************************************)

(** Get variable names in the components *)
module VarNames = struct
  
  open String.Set

  (** Names of var *)
  let of_var v =
    let Arr(ls) = v in
    of_list [String.concat ~sep:"." (List.map ls ~f:(fun (n, _) -> n))]

  (** Names of exp *)
  let rec of_exp e =
    match e with
    | Const(_)
    | Param(_) -> of_list []
    | Var(v) -> of_var v
    | Ite(f, e1, e2) -> union_list [of_form f; of_exp e1; of_exp e2]
  (** Names of formula *)
  and of_form f =
    match f with
    | Chaos
    | Miracle -> of_list []
    | Eqn(e1, e2) -> union_list [of_exp e1; of_exp e2]
    | Neg(form) -> of_form form
    | AndList(fl)
    | OrList(fl) -> union_list (List.map fl ~f:of_form)
    | Imply(f1, f2) -> union_list [of_form f1; of_form f2]


  let rec of_statement s =
    match s with
    | Assign(v, e) -> union_list [of_var v; of_exp e]
    | Parallel(slist) -> union_list (List.map slist ~f:of_statement)

  let of_rule r = 
    match r with
    | Rule(_, _, f, s) -> union_list [of_form f; of_statement s]
end





module VarNamesOfAssigns = struct
  
  open String.Set
  
  include VarNames

  let rec of_statement s =
    match s with
    | Assign(v, e) -> of_var v
    | Parallel(slist) -> union_list (List.map slist ~f:of_statement)

  let of_rule r =
    match r with
    | Rule(_, _, _, s) -> of_statement s

end




(*********************************** Module Variable Names, with Param values *****************)

(** Get variable names in the components *)
module VarNamesWithParam = struct
  
  open String.Set

  (** Names of exp *)
  let rec of_exp ~of_var e =
    match e with
    | Const(_)
    | Param(_) -> of_list []
    | Var(v) -> of_var v
    | Ite(f, e1, e2) -> union_list [of_form ~of_var f; of_exp ~of_var e1; of_exp ~of_var e2]
  (** Names of formula *)
  and of_form ~of_var f =
    match f with
    | Chaos
    | Miracle -> of_list []
    | Eqn(e1, e2) -> union_list [of_exp ~of_var e1; of_exp ~of_var e2]
    | Neg(form) -> of_form ~of_var form
    | AndList(fl)
    | OrList(fl) -> union_list (List.map fl ~f:(of_form ~of_var))
    | Imply(f1, f2) -> union_list [of_form ~of_var f1; of_form ~of_var f2]


  let rec of_statement ~of_var s =
    match s with
    | Assign(v, e) -> union_list [of_var v; of_exp ~of_var e]
    | Parallel(slist) -> union_list (List.map slist ~f:(of_statement ~of_var))

  let of_rule ~of_var r = 
    match r with
    | Rule(_, _, f, s) -> union_list [of_form ~of_var f; of_statement ~of_var s]
end
