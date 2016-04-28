(** Operations of formula based on Paramecium
*)

open Utils
open Paramecium
open Core.Std

(** Judge if a formula is tautology
    If negation of the formula is not satisfiable, then the formula is tautology

    @param filename is the temp file to store smt2 formula, default is "inv.smt2"
    @param quiet true (default) to prevent to print output of smt solver to screen
    @param types type definitions
    @param vardefs variable definitions
*)
let is_tautology ?(quiet=true) form =
  not (Smt.is_satisfiable ~quiet (ToStr.Smt2.form_of (neg form)))

(** Judge if a formula is satisfiable *)
let is_satisfiable ?(quiet=true) form =
  Smt.is_satisfiable ~quiet (ToStr.Smt2.form_of form)

let rec eliminate_imply_neg ?(eli_eqn=false)  form =
  match form with
  | Chaos
  | Miracle
  | Eqn(_) -> form
  | Neg(Chaos) -> miracle
  | Neg(Miracle) -> chaos
  | Neg(Eqn(Const(Boolc(true)), e1))
  | Neg(Eqn(e1, Const(Boolc(true)))) ->
    if eli_eqn then eqn e1 (Const(Boolc(false))) else begin form end
  | Neg(Eqn(Const(Boolc(false)), e1))
  | Neg(Eqn(e1, Const(Boolc(false)))) ->
    if eli_eqn then eqn e1 (Const(Boolc(true))) else begin form end
  | Neg(Eqn(_)) -> form
  | Neg(Neg(f)) -> eliminate_imply_neg ~eli_eqn f
  | Neg(AndList(fl)) -> eliminate_imply_neg ~eli_eqn (orList (List.map fl ~f:neg))
  | Neg(OrList(fl)) -> eliminate_imply_neg ~eli_eqn (andList (List.map fl ~f:neg))
  | Neg(Imply(f1, f2)) -> eliminate_imply_neg ~eli_eqn (andList [f1; neg f2])
  | AndList(fl) -> andList (List.map fl ~f:(eliminate_imply_neg ~eli_eqn))
  | OrList(fl) -> orList (List.map fl ~f:(eliminate_imply_neg ~eli_eqn))
  | Imply(f1, f2) -> eliminate_imply_neg ~eli_eqn (orList [neg f1; f2])

(** Cast a formula to a list of formulae with and relation between them *)
let flat_and_to_list form =
  let no_imply_neg = eliminate_imply_neg form in
  let rec wrapper form =
    match form with
    | Chaos
    | Miracle
    | Eqn(_)
    | Neg(Eqn(_)) -> [form]
    | AndList([]) -> [chaos]
    | AndList([f]) -> [f]
    | AndList(fl) -> List.concat (List.map fl ~f:wrapper)
    | OrList([]) -> [miracle]
    | OrList([f]) -> [f]
    | OrList(fl) -> [form]
    | Neg(_)
    | Imply(_) -> raise Empty_exception
  in
  wrapper no_imply_neg

(** For andList, flat its all components,
    for others, flat to a single list
*)
let flat_to_andList form =
  andList (flat_and_to_list form)

(** Cast a formula to a list of formulae with or relation between them *)
let flat_or_to_list form =
  let no_imply_neg = eliminate_imply_neg form in
  let rec wrapper form =
    match form with
    | Chaos
    | Miracle
    | Eqn(_)
    | Neg(Eqn(_))
    | AndList(_) -> [form]
    | OrList(fl) -> List.concat (List.map fl ~f:wrapper)
    | Neg(_)
    | Imply(_) -> raise Empty_exception
  in
  wrapper no_imply_neg

(** For orList, flat its all components,
    for others, flat to a single list
*)
let flat_to_orList form =
  orList (flat_or_to_list form)

let rec remove_inner_andList form =
  match form with
  | Chaos
  | Miracle
  | Eqn(_)
  | Neg(Eqn(_)) -> [form]
  | AndList(fl) -> List.concat (List.map fl ~f:remove_inner_andList)
  | OrList(fl) -> [orList (List.concat (List.map fl ~f:remove_inner_orList))]
  | Neg(_)
  | Imply(_) -> Prt.error (ToStr.Smv.form_act form); raise Empty_exception
and remove_inner_orList form =
  match form with
  | Chaos
  | Miracle
  | Eqn(_)
  | Neg(Eqn(_)) -> [form]
  | AndList(fl) -> [andList (List.concat (List.map fl ~f:remove_inner_andList))]
  | OrList(fl) -> List.concat (List.map fl ~f:remove_inner_orList)
  | Neg(_)
  | Imply(_) -> Prt.error (ToStr.Smv.form_act form); raise Empty_exception


let rec forms_dedup forms =
  let forms' = List.map forms ~f:dedup in
  let rec wrapper forms res set =
    match forms with
    | [] -> res
    | f::forms' ->
      begin
        let key = ToStr.Debug.form_act f in
        match String.Set.find set ~f:(fun g -> g = key) with
        | Some(_) -> wrapper forms' res set
        | None -> wrapper forms' (res@[f]) (String.Set.add set key)
      end
  in
  wrapper forms' [] String.Set.empty
and dedup form =
  match form with
  | Chaos
  | Miracle
  | Eqn(_) -> form
  | Neg(f) -> neg (dedup f)
  | AndList(fl) -> andList (forms_dedup fl)
  | OrList(fl) -> orList (forms_dedup fl)
  | Imply(f1, f2) -> imply (dedup f1) (dedup f2)

(** Simplify a formula *)
let simplify ?(eli_eqn=false) form =
  let no_imply_neg = eliminate_imply_neg ~eli_eqn form in
  let rec wrapper form =
    match form with
    | Chaos -> chaos
    | Miracle -> miracle
    | Neg(Chaos) -> miracle
    | Neg(Miracle) -> chaos
    | Eqn(_)
    | Neg(Eqn(_)) ->
      if is_tautology form then chaos
      else if not (is_satisfiable form) then miracle
      else begin form end
    | AndList(ls) ->
      let simplified_ls = List.map ls ~f:wrapper in
      if List.exists simplified_ls ~f:(fun x -> x = Miracle) then miracle
      else begin
        let not_chaos = forms_dedup (List.filter simplified_ls ~f:(fun x -> not (x = Chaos))) in
        let or_coms = List.map not_chaos ~f:(fun x ->
          match x with
          | OrList(ors) -> ors
          | _ -> [x]
        ) in
        let eliminate_inner_and_of_list ls =
          List.concat (List.map ls ~f:(fun x -> match x with | AndList(ls) -> ls | _ -> [x]))
        in
        match cartesian_product or_coms with
        | [] -> chaos
        | [[one]] -> one
        | [andls] -> andList (eliminate_inner_and_of_list andls)
        | orls -> orList (List.map orls ~f:(fun c ->
          match c with
          | [x] -> x
          | _ -> andList (eliminate_inner_and_of_list c)
        ))
      end
    | OrList(ls) ->
      let simplified_ls = List.map ls ~f:wrapper in
      if List.exists simplified_ls ~f:(fun x -> x = Chaos) then chaos
      else begin
        let not_miracle = forms_dedup (List.filter simplified_ls ~f:(fun x -> not (x = Miracle))) in
        let no_inner_or = 
          List.map not_miracle ~f:(fun x -> match x with | OrList(ls) -> ls | _ -> [x])
        in
        match List.concat no_inner_or with
        | [] -> miracle
        | [one] -> one
        | orls -> orList orls
      end
    | Neg(_)
    | Imply(_) -> Prt.error (ToStr.Smv.form_act form); raise Empty_exception
  in
  wrapper no_imply_neg

(** Raises when there are many parameter references more than range of its type *)
exception Too_many_parameters_of_same_type

(** Normalize a parameterized formula *)
let normalize form ~types =
  let (_, pfs, form') = Generalize.form_act form in
  let pf_groups = partition pfs ~f:typename_of_paramfix in
  (*Prt.warning (String.concat ~sep:";" (
    List.map pf_groups ~f:(fun x -> String.concat (List.map x ~f:ToStr.Debug.paramref_act))
  )^", "^String.concat ~sep:";" (
    List.map [pfs] ~f:(fun x -> String.concat (List.map x ~f:ToStr.Debug.paramref_act))
  )^"\n");*)
  (* e.g. cast [3;1;2;1] to [a;b;c;b] then to [1;2;3;2] *)
  let normalize_type pfs =
    let rec gen_map pfs range m =
      match pfs with
      | [] -> m
      | pf::pfs' ->
        let key = ToStr.Smv.paramref_act pf in (
          match Map.find m key with
          | None -> (
              let vname = name_of_param pf in
              let tname = typename_of_paramfix pf in
              (* TODO *)
              (* 暂时特殊处理参数0 *)
              if pf = paramfix vname tname (intc 0) then
                gen_map pfs' range (Map.add m ~key ~data:pf)
              else begin
                match range with
                | [] -> (
                    match List.filter (name2type ~tname ~types) ~f:(fun v -> not (v = intc 0)) with
                    | [] -> raise Empty_exception
                    | v::range' -> gen_map pfs' range' (Map.add m ~key ~data:(paramfix vname tname v))
                  )
                | v::range' -> gen_map pfs' range' (Map.add m ~key ~data:(paramfix vname tname v))
              end
            )
          | Some(_) -> gen_map pfs' range m
        )
    in
    let m = gen_map pfs [] (String.Map.empty) in
    List.map pfs ~f:(fun pf -> Map.find_exn m (ToStr.Smv.paramref_act pf))
  in
  let p = List.concat (List.map pf_groups ~f:normalize_type) in
  (*Prt.warning ("Normalize: "^ToStr.Smv.form_act form^", "
    ^ToStr.Debug.form_act (apply_form form' ~p)^", "^
    (String.concat (List.map p ~f:ToStr.Debug.paramref_act))^"\n"
  );*)
  apply_form form' ~p









(* partition the concrete params by their type, then sort by typename *)
let sorted_partition params =
  partition_with_label params ~f:typename_of_paramfix
  |> List.sort ~cmp:(fun (x, _) (y, _) -> String.compare x y)

(*  Given two partitioned concrete params, suppose they have same types
    Judge if the first partition has no more parameters in each type
    than the second one
*)
let not_more_params partition1 partition2 =
  let not_more_than (_, x) (_, y) = List.length x <= List.length y in
  List.map2_exn partition1 partition2 ~f:not_more_than
  |> reduce ~default:true ~f:(fun x y -> x && y)

(*  If partition1 is the compatible subset of one with partition2
    Generate the compatible parameters
*)
let compatible_params 
(partition1:(string * paramref list) list) 
(partition2:(string * paramref list) list) =
  (* parameter names of eache type in partition2 *)
  let params_names_part2 = List.map partition2 ~f:(fun (_, x) -> List.map x ~f:name_of_param) in
  (* parameter count of each type in partition2 *)
  let params_c_part2 = List.map partition2 ~f:(fun (_, x) -> List.length x) in
  (* get values of parameters of shortened partition1 *)
  let params_val_shorten_part1 = List.map partition1 ~f:(fun (_, x) -> x) in
  let rename_all names ls = List.map ls ~f:(fun vs -> List.map2_exn vs names ~f:set_param_name) in
  (*  choose |params2[k]| params in the values of shortened partition1
      result is like [[[a;b];[b;c];[a;c]]; [[1;2];[1;3];[2;3]]]
  *)
  List.map2_exn params_val_shorten_part1 params_c_part2 ~f:combination
  (*  permutation,  result is like
      [[[a;b];[b;a];[b;c];[c;b];[a;c];[c;a]]; [[1;2];[2;1];...]]
  *)
  |> List.map ~f:(fun x -> List.concat (List.map x ~f:(fun y -> permutation y)))
  (* rename to names of partition2 *)
  |> List.map2_exn params_names_part2 ~f:rename_all
  (* result is like [[[a;b];[1;2]]; [[a;b];[2;1]]; ...] *)
  |> cartesian_product
  (* result is like [[a;b;1;2]; [a;b;2;1]; ...] *)
  |> List.map ~f:List.concat

(* Algorithm ParamCompatible
    This algorithm is for judge if a invariant inv1 is compatible with inv2.

    Compatible definition
    Suppose parameter type set of inv1 is types1, and types2 of inv2; suppose
    |types1| = m, |types2| = n; inv1 is
    compatible with inv2 iff:
    1. types2 is subset of types1 (so n <= m), and
    2. suppose the parameter types in inv1 have parameter sets params1[i] for
      0 <= i < m, and for inv2 have paramter sets params2[j] for 0 <= j < n, then
      |params2[k]| <= |params1[k]| for 0 <= k < n

    This algorithm returns the compatible params combination of inv1 for inv2
    if are compatible, else return []
*)
let param_compatible 
(inv_param1:paramref list) 
(inv_param2:paramref list) =
  (* Firstly, partition the parameters by their type *)
  let partition1 = sorted_partition inv_param1 in
  let partition2 = sorted_partition inv_param2 in
  (* Secondly, Judge the compatibility *)
  let types1 = String.Set.of_list (List.map partition1 ~f:(fun (x, _) -> x)) in
  let types2 = String.Set.of_list (List.map partition2 ~f:(fun (x, _) -> x)) in
  (* types2 is not subset of types1 *)
  if not (String.Set.subset types2 types1) then
    []
  else begin
    let shorten_partition1 = List.sub partition1 ~pos:0 ~len:(List.length partition2) in
    let more_params = not (not_more_params partition2 shorten_partition1) in
    (* |params2[k]| > |params1[k| for 0 <= k < n *)
    if more_params then
      []
    (* is compatible *)
    else begin
      compatible_params shorten_partition1 partition2
    end
  end

(* Decide if formula cons could be implied by ant *)
let can_imply ant cons =
  let ant_vars = VarNames.of_form ant in
  let cons_vars = VarNames.of_form cons in
  let (ant_pd, ant_p, ant_gened) = Generalize.form_act ant in
  let (_, cons_p, _) = Generalize.form_act cons in
  (* If vars in old are more than vars in inv, then can't imply *)
  (* TODO is there some problems in this strategy? *)
  if String.Set.length (String.Set.diff ant_vars cons_vars) > 0 then
    None
  (* If length of parameters in old is 0, then check directly *)
  else if List.length ant_pd = 0 then
    if is_tautology (imply (simplify ant) cons) then Some ant
    else begin None end
  (* If old has more paramters, then false *)
  else if param_compatible cons_p ant_p = [] then None
  (* Otherwise, check old with parameters of inv *)
  (*else if form_are_symmetric inv old then Some old*)
  else begin
    let params = param_compatible cons_p ant_p in
    let rec has_implied params =
      match params with
      | [] -> None
      | p::params' ->
        let new_ant = apply_form ant_gened ~p in
        if is_tautology (imply new_ant cons) then
          Some new_ant
        else begin
          has_implied params'
        end
    in
    has_implied params
  end

let symmetry_form f1 f2 =
  match can_imply f1 f2, can_imply f2 f1 with
  | Some(_), Some(_) -> 0
  | _ -> String.compare (ToStr.Smv.form_act f1) (ToStr.Smv.form_act f2)
