(** For find invariants and causal relations based on Paramecium
*)

open Utils
open Formula
open Paramecium

open Core.Std
open Re2

(** Raised when parallel statements haven't been cast to assign list *)
exception Unexhausted_flat_parallel

(** Raised when circular parallel assignments detected *)
exception Circular_parallel_assign

(** Raised when require to check a inv has too many paramters *)
exception Parameter_overflow

exception Invariant_not_sat_on_init of string

(** Concrete rule

    + ConcreteRule: instantiated rule, concrete param list
    + AllRuleInst: all instances of the rule has same relation
*)
type concrete_rule =
  | ConcreteRule of string * paramref list
  | AllRuleInst of string
with sexp

let concrete_rule r ps =
  let Rule(name, _, _, _) = r in
  ConcreteRule(name, ps)

let all_rule_inst r =
  let Rule(name, _, _, _) = r in
  AllRuleInst(name)

let all_rule_inst_from_name n =
  AllRuleInst(n)

(** Concrete property

    + ConcreteProp: property, concrete param list
*)
type concrete_prop =
  | ConcreteProp of prop * paramref list
with sexp

let concrete_prop property ps = ConcreteProp(property, ps)

(** Causal relations

  + InvHoldForRule1
  + InvHoldForRule2
  + InvHoldForRule3: the new concrete invariant found
*)
type relation =
  | InvHoldForRule1
  | InvHoldForRule2
  | InvHoldForRule3 of concrete_prop
with sexp

let invHoldForRule1 = InvHoldForRule1
let invHoldForRule2 = InvHoldForRule2
let invHoldForRule3 p = InvHoldForRule3 p

(** InvFinder type, i.e., causal relation table *)
type t = {
  rule: concrete_rule;
  inv: concrete_prop;
  branch: concrete_prop;
  relation: relation;
}
with sexp

let type_defs = ref []
let protocol_name = ref ""
let raw_rule_table = Hashtbl.create ~hashable:String.hashable ()
let rule_table = Hashtbl.create ~hashable:String.hashable ()
let rule_vars_table = Hashtbl.create ~hashable:String.hashable ()

let get_rname_of_crname crname =
  Regex.rewrite_exn (Regex.of_string "\\[.+?\\]") ~template:"" crname

let rec cache_vars_of_rules rs =
  match rs with
  | [] -> ()
  | r::rs' ->
    let Rule(key, _, _, _) = r in
    Hashtbl.replace rule_vars_table ~key ~data:(VarNamesOfAssigns.of_rule r);
    cache_vars_of_rules rs'

(* Convert statements to a list of assignments *)
let rec statement_2_assigns statement =
  match statement with
  | Parallel(sl) -> List.concat (List.map sl ~f:statement_2_assigns)
  | Assign(v, e) -> [(v, e)]

let simplify_inst_guard r =
  let Rule(n, p, f, s) = r in
  rule n p (simplify f) s

(* Convert rule to concrete rules *)
let rule_2_concrete r ps =
  let r_insts =
    if List.length ps = 0 then [(simplify_inst_guard r, [])]
    else List.map ps ~f:(fun p -> simplify_inst_guard (apply_rule r ~p), p)
  in
  let rec store_rules rs =
    match rs with
    | [] -> ()
    | (ri, p)::rs' ->
      let Rule(name, _, guard, statement) = ri in
      let guards = flat_and_to_list (guard) in
      let assigns = statement_2_assigns statement in
      Hashtbl.replace rule_table ~key:name ~data:(ri, concrete_rule ri p, guards, assigns);
      store_rules rs'
  in
  store_rules r_insts;;

(* Convert concrete rule to rule instances *)
let concrete_rule_2_rule_inst cr =
  let ConcreteRule(rname, _) = cr in
  match Hashtbl.find rule_table rname with
  | Some(r) -> r
  | None ->
    Prt.error (sprintf "%s not in [%s]" rname (String.concat ~sep:", " (Hashtbl.keys rule_table)));
    raise Empty_exception

(* Convert concrete property to formula *)
let concrete_prop_2_form cprop =
  let ConcreteProp(property, pfs) = cprop in
  let Prop(_, _, form) = property in
  apply_form form ~p:pfs

(* Convert formula to concrete property *)
let form_2_concreate_prop ?(id=0) ?(rename=true) form =
  let new_inv_name_base = "inv__" in
  (* Generate names for new invariants found *)
  let next_inv_name id = sprintf "%s%d" new_inv_name_base id in
  let (pds, pfs, form') = Generalize.form_act ~rename form in
  let property = prop (next_inv_name id) pds form' in
  concrete_prop property pfs

(** Convert relation to a string *)
let relation_2_str relation =
  match relation with
  | InvHoldForRule1 -> "invHoldForRule1"
  | InvHoldForRule2 -> "invHoldForRule2"
  | InvHoldForRule3(cp) -> 
    let form = (concrete_prop_2_form cp) in
    let ConcreteProp(Prop(pname, _, _), _) = cp in
    sprintf "invHoldForRule3-%s:%s" pname (ToStr.Smv.form_act form)

(** Convert t to a string *)
let to_str {rule; inv; branch; relation} =
  let rname =
    match rule with
    | ConcreteRule(rname, _)
    | AllRuleInst(rname) -> rname
  in
  let inv_str = ToStr.Smv.form_act (concrete_prop_2_form inv) in
  let branch_str = ToStr.Smv.form_act (concrete_prop_2_form branch) in
  let rel_str = relation_2_str relation in
  sprintf "rule: %s; inv: %s; g: %s; rel: %s" rname inv_str branch_str rel_str





let get_rule_inst_name rname pfs =
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
  sprintf "%s%s" rname (String.concat (List.map pfs ~f:paramref_act))

let sort_pfs pds pfs =
  (*Prt.info (String.concat ~sep:", " (List.map pds ~f:(fun (Paramdef(n, _)) -> n)));
  Prt.warning (String.concat ~sep:", " (List.map pfs ~f:(fun (Paramfix(n, _, _)) -> n)));*)
  List.map pds ~f:(fun (Paramdef(name, _)) ->
    List.find_exn pfs ~f:(fun pr ->
      match pr with
      | Paramfix(n, _, _) -> n = name
      | _ -> raise Empty_exception
    )
  )




(* Evaluate exp with assignments
    Result has format (condition, value)
*)
let rec exp_eval exp ~assigns =
  match exp with
  | Const(_) -> [(chaos, exp)]
  | Param(Paramref _) -> raise Unexhausted_inst
  | Param(_) -> [(chaos, exp)]
  | Var(v) ->
    let value = List.Assoc.find assigns v ~equal:(fun x y ->
      ToStr.Smv.var_act x = ToStr.Smv.var_act y
    ) in (
      match value with
      | None -> [(chaos, var v)]
      | Some(e) ->
        let rec analyze_exp e =
          match e with
          | Ite(f, e1, e2) ->
            let f1 =
              let ff = simplify f in
              match ff with
              | OrList(fl) -> fl
              | _ -> [ff]
            in
            let f2 =
              let ff = simplify (neg f) in
              match ff with
              | OrList(fl) -> fl
              | _ -> [ff]
            in
            let res1 = List.concat (List.map (analyze_exp e1) ~f:(fun (g, e) ->
              List.map f1 ~f:(fun f -> andList [g; f], e)
            )) in
            let res2 = List.concat (List.map (analyze_exp e2) ~f:(fun (g, e) ->
              List.map f2 ~f:(fun f -> andList [g; f], e)
            )) in
            res1@res2
          | _ -> [(chaos, e)]
        in
        List.map (analyze_exp e) ~f:(fun (g, e) -> simplify g, e)
    )
  | UIF(n, el) ->
    let evaled = List.map el ~f:(exp_eval ~assigns) in
    let mixed = cartesian_product evaled in
    List.map mixed ~f:(fun ls ->
      let guards, exps = List.unzip ls in
      andList guards, uif n exps
    )
  | Ite(f, e1, e2) -> raise Empty_exception
(* Evaluate formula with assignments
    Result has format (condition, form)
*)
and form_eval form ~assigns =
  match form with
  | Chaos
  | Miracle -> [(chaos, form)]
  | UIP(n, el) ->
    let evaled = List.map el ~f:(exp_eval ~assigns) in
    let mixed = cartesian_product evaled in
    List.map mixed ~f:(fun ls ->
      let guards, exps = List.unzip ls in
      andList guards, uip n exps
    )
  | Eqn(e1, e2) ->
    let res1 = exp_eval e1 ~assigns in
    let res2 = exp_eval e2 ~assigns in
    let mixed = cartesian_product [res1; res2] in
    List.map mixed ~f:(fun [(g1, e1); (g2, e2)] ->
      simplify (andList [g1; g2]), eqn e1 e2
    )
  | Neg(f) -> List.map (form_eval f ~assigns) ~f:(fun (g, f) -> g, neg f)
  | AndList(fl) ->
    let mixed = cartesian_product (List.map fl ~f:(form_eval ~assigns)) in
    List.map mixed ~f:(fun pairs ->
      let gs, fl' = List.unzip pairs in
      simplify (andList gs), andList fl'
    )
  | OrList(fl) ->
    let mixed = cartesian_product (List.map fl ~f:(form_eval ~assigns)) in
    List.map mixed ~f:(fun pairs ->
      let gs, fl' = List.unzip pairs in
      simplify (andList gs), orList fl'
    )
  | Imply(ant, cons) ->
    let res1 = form_eval ant ~assigns in
    let res2 = form_eval cons ~assigns in
    let mixed = cartesian_product [res1; res2] in
    List.map mixed ~f:(fun [(g1, ant'); (g2, cons')] ->
      simplify (andList [g1; g2]), imply ant' cons'
    )

(* pre_cond *)
let pre_cond f assigns = form_eval f ~assigns



(* Minify inv by remove useless components one by one *)
let minify_inv_desc inv =
  let rec wrapper necessary parts =
    match parts with
    | [] ->
      if Smv.is_inv (ToStr.Smv.form_act (neg (andList necessary))) then
        necessary
      else begin raise Empty_exception end
    | p::parts' ->
      if Smv.is_inv (ToStr.Smv.form_act (neg (andList (necessary@parts')))) then
        wrapper necessary parts'
      else begin
        wrapper (p::necessary) parts'
      end
  in
  let ls = match inv with | AndList(fl) -> fl | _ -> [inv] in
  andList (wrapper [] ls)

(* Minify inv by add useful components gradually *)
let minify_inv_inc inv =
  Prt.info (sprintf "to be minified: %s" (ToStr.Smv.form_act inv));
  let ls = match inv with | AndList(fl) -> fl | _ -> [inv] in
  let components = combination_all ls in
  let _len = List.length components in
  let rec wrapper components =
    match components with
    | [] -> 
      Prt.error ("Not invariant: "^ToStr.Smv.form_act inv);
      raise Empty_exception
    | parts::components' ->
      Prt.info (sprintf "minifing %d/%d" (_len - List.length components') _len);
      let piece = normalize (andList parts) ~types:(!type_defs) in
      let check_inv_res =
        let (_, pfs, _) = Generalize.form_act piece in
        (* TODO *)
        let over = List.filter pfs ~f:(fun pr ->
          match pr with
          | Paramfix(_, _, Intc(i)) -> i > 3
          | _ -> false
        ) in
        let check_with_murphi form =
          let form_str = ToStr.Smv.form_act ~lower:false (neg form) in
          let res = Murphi.is_inv form_str in
          print_endline (sprintf "Check by mu: %s, %b" form_str res); res
        in
        if List.is_empty over then
          try Smv.is_inv (ToStr.Smv.form_act (neg piece)) && ((not !Cmdline.confirm_with_mu) || check_with_murphi piece) with
          | Client.Smv.Cannot_check -> check_with_murphi piece
          | _ -> raise Empty_exception
        else begin
          check_with_murphi piece
        end
      in
      if check_inv_res then andList parts
      else begin wrapper components' end
  in
  wrapper components







module InvLib = struct
  
  let index = ref 1

  let pairs = ref []

  let add inv =
    let inv = normalize inv ~types:(!type_defs) in
    match List.find (!pairs) ~f:(fun (p, _) -> symmetry_form p inv = 0) with
    | Some(_, cinv) -> cinv
    | None ->
      let cinv = form_2_concreate_prop ~id:(!index) inv in
      incr index;
      pairs := ((!pairs)@[(inv, cinv)]);
      cinv

  let add_many invs = List.dedup (List.map invs ~f:add)

  let get_all_cinvs () = List.map (!pairs) ~f:(fun (_, cinv) -> cinv)

  let any_can_be_implied_by inv =
    let rec wrapper invs =
      match invs with
      | [] -> None
      | (old, c_old)::invs' ->
        let res = can_imply (neg old) (neg inv) in
        match res with
        | None -> wrapper invs'
        | Some(f) ->
          let f = simplify (neg f) in
          let ConcreteProp(Prop(pname, _, _), _) = c_old in
          let ConcreteProp(Prop(_, ppds, pform), ppfs) = form_2_concreate_prop f in
          Some (concrete_prop (prop pname ppds pform) ppfs)
    in
    wrapper (!pairs)


end







(********************************** Module Choose **************************************)

(* Choose a true invariant *)
module Choose = struct

  type level =
    | Tautology of formula
    | Implied of concrete_prop
    | New_inv of formula
    | Not_inv

  let tautology form = Tautology(form)
  let implied old = Implied(old)
  let new_inv form = New_inv(form)
  let not_inv = Not_inv

  (* Check the level of an optional invariant *)
  let check_level ?(must_new=false) inv =
    let inv = simplify ~eli_eqn:true inv in
    if is_tautology (neg inv) then
      tautology inv
    else begin
      try
        let inv = minify_inv_inc inv in
        (* Because invs are in form of negation, so inv -> old means neg old -> neg inv *)
        let implied_by_old = InvLib.any_can_be_implied_by inv in
        match implied_by_old with
        | Some(old) -> implied old
        | None ->
          let normalized = normalize inv ~types:(!type_defs) in
          if must_new || Smv.is_inv (ToStr.Smv.form_act (neg normalized)) then
            new_inv inv
          else begin
            not_inv
          end
      with
      | _ -> not_inv
    end

  (* choose new inv *)
  let choose guards assigns cons =
    check_level ~must_new:true (simplify (andList (cons::guards)))

end










module SemiPerm = struct

  let semi_table = Hashtbl.create ~hashable:String.hashable ()

  let equal_int a b m n = not ((a <= m - n) && (not (a = b)))

  let equal_list ls1 ls2 m n =
    if List.length ls1 = List.length ls2 && List.length ls1 > 0 then
      let flags = List.map (List.zip_exn ls1 ls2) ~f:(fun (x, y) -> equal_int x y m n) in
      all flags ~f:(fun flag -> flag = true)
    else begin false end

  let equal ls1 ls2 m n =
    (equal_list ls1 ls2 m n) || (equal_list (List.rev ls1) (List.rev ls2) m n)

  let rec semi ls m n =
    match ls with
    | [] -> []
    | ele::ls' ->
      let not_equal = List.filter ls' ~f:(fun x -> not (equal ele x m n)) in
      ele::(semi not_equal m n)

  let semi_perm m n =
    match (m, n) with
    | (m, 0) -> [[]]
    | (0, n) -> []
    | _ -> 
      let nums = List.map (up_to m) ~f:(fun x -> x + 1) in
      semi (combination_permutation nums n) m n

  let gen_of_a_type inv_pds rule_pds =
    match rule_pds with
    | [] -> raise Empty_exception
    | (Paramdef(_, tname))::_ ->
      let trange = name2type ~tname ~types:(!type_defs) in
      let n_inv = List.length inv_pds in
      let n_rule = List.length rule_pds in
      let semi_list = semi_perm (n_inv + n_rule) n_rule in
      let semi_consts = List.map semi_list ~f:(fun ls -> List.map ls ~f:(fun x -> intc x)) in
      List.map semi_consts ~f:(fun ls ->
        List.map2_exn ls rule_pds ~f:(fun c (Paramdef(name, _)) -> paramfix name tname c)
      )


  let gen_paramfixes inv_pds rule_pds =
    let key = String.concat ~sep:";" (List.map (inv_pds@rule_pds) ~f:(fun (Paramdef(name, tname)) ->
      sprintf "%s:%s" name tname
    )) in
    match Hashtbl.find semi_table key with
    | None ->
      let inv_parts = partition_with_label inv_pds ~f:(fun (Paramdef(_, tname)) -> tname) in
      let rule_parts = partition_with_label rule_pds ~f:(fun (Paramdef(_, tname)) -> tname) in
      let paramfixes = 
        List.map rule_parts ~f:(fun (tname, rpds) ->
          let ipds = 
            match List.Assoc.find inv_parts tname with
            | None -> []
            | Some(ls) -> ls
          in
          gen_of_a_type ipds rpds
        )
        |> cartesian_product
        |> List.map ~f:List.concat
      in
      let pf_unsym =
        let all_pfs = cart_product_with_paramfix rule_pds (!type_defs) in
        (* TODO *)
        let has_unsym pfs = List.exists pfs ~f:(fun pr -> 
          match pr with 
          | Paramfix(_, _, c) -> c = intc 0
          | _ -> raise Empty_exception
        ) in
        List.filter all_pfs ~f:has_unsym
      in
      let res = List.map (paramfixes@pf_unsym) ~f:(sort_pfs rule_pds) in
      Hashtbl.replace semi_table ~key ~data:res; res
    | Some(res) -> res

end





module Storage = struct

  let append_file fn lines =
    let f = Out_channel.create fn ~append:true in
    Out_channel.output_lines f lines;
    Out_channel.close f;;
  
  let add_many filename key values convertor =
    let name = sprintf "%s.%s.cache" filename key in
    let strs =
      values
      |> List.map ~f:convertor
      |> List.map ~f:Sexp.to_string
    in
    append_file name strs

  let add filename key value convertor = add_many filename key [value] convertor

  let replace_many filename key values convertor =
    let name = sprintf "%s.%s.cache" filename key in
    let strs =
      values
      |> List.map ~f:convertor
      |> List.map ~f:Sexp.to_string
    in
    Out_channel.write_lines name strs

  let replace filename key value convertor =
    let name = sprintf "%s.%s.cache" filename key in
    let str = Sexp.to_string (convertor value) in
    Out_channel.write_all name str

  let get_many filename key default convertor =
    let name = sprintf "%s.%s.cache" filename key in
    try
      In_channel.read_lines name
      |> List.map ~f:Sexp.of_string
      |> List.map ~f:convertor
    with
    | Sys_error(_) -> default
    | e -> raise e

  let get filename key default convertor =
    let name = sprintf "%s.%s.cache" filename key in
    try
      convertor (Sexp.of_string (In_channel.read_all name))
    with
    | Sys_error(_) -> default
    | e -> raise e

end







(** Rename the parameters in a concrete component with given paramfixes
    of concrete rules and concrete properties *)
module RenameParam = struct
  
  let pfs_rule_ref = ref []
  let pfs_prop_ref = ref []

  let paramref_act pr =
    match pr with
    | Paramref(_) -> raise Empty_exception
    | Paramfix(_, tn, c) ->
      let pfs_are_match (Paramfix(_, tn', c')) = tn = tn' && c = c' in
      begin
        match List.find (!pfs_prop_ref) ~f:pfs_are_match with
        | Some(pf) -> pf
        | None ->
          begin
            match List.find (!pfs_rule_ref) ~f:pfs_are_match with
            | Some(pf) -> pf
            | None -> pr
          end
      end

  let var_act (Arr(ls)) =
    arr (List.map ls ~f:(fun (name, prs) ->
      name, List.map prs ~f:paramref_act
    ))

  let rec exp_act e =
    match e with
    | Const(_) -> e
    | Var(v) -> var (var_act v)
    | Param(pr) -> param (paramref_act pr)
    | Ite(f, e1, e2) -> ite (form_act f) (exp_act e1) (exp_act e2)
    | UIF(n, el) -> uif n (List.map el ~f:exp_act)
  and form_act ?(pfs_rule=(!pfs_rule_ref)) ?(pfs_prop=(!pfs_prop_ref)) f =
    pfs_rule_ref := pfs_rule;
    pfs_prop_ref := pfs_prop;
    match f with
    | Chaos
    | Miracle -> f
    | UIP(n, el) -> uip n (List.map el ~f:exp_act)
    | Eqn(e1, e2) -> eqn (exp_act e1) (exp_act e2)
    | Neg(g) -> neg (form_act g)
    | AndList(fl) -> andList (List.map fl ~f:form_act)
    | OrList(fl) -> orList (List.map fl ~f:form_act)
    | Imply(f1, f2) -> imply (form_act f1) (form_act f2)

end







  


(* Deal with case invHoldForRule1 *)
let deal_with_case_1 crule cinv g =
  { rule = crule;
    inv = cinv;
    branch = g;
    relation = invHoldForRule1;
  }

(* Deal with case invHoldForRule2 *)
let deal_with_case_2 crule cinv g =
  { rule = crule;
    inv = cinv;
    branch = g;
    relation = invHoldForRule2;
  }

(* Deal with case invHoldForRule3 *)
let deal_with_case_3 crule cinv cons g =
  let Rule(name, _, guard, statement), _, guards, assigns = concrete_rule_2_rule_inst crule in
  let level = Choose.choose (concrete_prop_2_form g::guards) assigns cons in
  let (new_inv, causal_cinv) =
    match level with
    | Choose.Tautology(_) -> ([], form_2_concreate_prop chaos)
    | Choose.Implied(old) -> ([], old)
    | Choose.New_inv(inv) ->
      let new_inv_str = ToStr.Smv.form_act inv in
      let old_inv_str = ToStr.Smv.form_act (concrete_prop_2_form cinv) in
      print_endline (sprintf "rule %s, new %s, old %s" name new_inv_str old_inv_str);
      ([inv], form_2_concreate_prop inv)
    | Choose.Not_inv ->
      let ConcreteRule(n, ps) = crule in
      let cp_2_str pr =
        match pr with
        | Paramref(_) -> raise Empty_exception
        | Paramfix(n, _, _) -> sprintf "%s:%s" n (ToStr.Smv.paramref_act pr)
      in
      let params_str = String.concat (List.map ps ~f:cp_2_str) ~sep:", " in
      let inv_str = ToStr.Smv.form_act (concrete_prop_2_form cinv) in
      let guard_str = ToStr.Smv.form_act guard in
      Prt.error (sprintf "\n\n%s, %s\nguard: %s\ninv: %s\n" n params_str guard_str inv_str);
      raise Empty_exception
  in
  let ConcreteProp(Prop(_, _, f), _) = causal_cinv in
  if f = chaos then
    [], deal_with_case_1 crule cinv g
  else
  (new_inv, { rule = crule;
    inv = cinv;
    branch = g;
    relation = invHoldForRule3 causal_cinv;
  })


(* Find new inv and relations with concrete rule and a concrete invariant *)
let tabular_expans (Rule(_name, _, form, _), crule, _, assigns) ~cinv =
  let ConcreteRule(_, pfs_rule) = crule in
  let ConcreteProp(_, pfs_prop) = cinv in
  let inv_inst = simplify (concrete_prop_2_form cinv) in
  (* pre_cond *)
  let obligations =
    pre_cond inv_inst assigns
    |> List.map ~f:(fun (g, o) -> g, simplify o)
    |> List.filter ~f:(fun (g, _) -> is_satisfiable g)
  in
  Prt.info (sprintf "rule: %s; inv: %s" _name (ToStr.Smv.form_act inv_inst));
  let rec deal_with_case obligations relations =
    match obligations with
    | [] -> relations
    | (g, obligation)::obligations' ->
      let branch =
        RenameParam.form_act ~pfs_rule ~pfs_prop g
        |> form_2_concreate_prop ~rename:false
      in
      let relation = 
        (* case 2 *)
        if obligation = inv_inst || symmetry_form obligation inv_inst = 0 then
          ([], deal_with_case_2 crule cinv branch)
        (* case 1 *)
        else if is_tautology (imply form (neg obligation)) then
          ([], deal_with_case_1 crule cinv branch)
        (* case 3 *)
        else begin
          deal_with_case_3 crule cinv obligation branch
        end
      in
      deal_with_case obligations' (relations@[relation])
  in
  deal_with_case obligations []

let compute_rule_inst_names rname_paraminfo_pairs prop_pds =
  List.map rname_paraminfo_pairs ~f:(fun (rname, rpds) ->
    match rpds with
    | [] ->
      begin
        match Hashtbl.find rule_table rname with
        | None ->
          let ri = Hashtbl.find_exn raw_rule_table rname in
          let Rule(_, _, guard, statement) = ri in
          let guards = flat_and_to_list guard in
          let assigns = statement_2_assigns statement in
          let data = (ri, concrete_rule ri [], guards, assigns) in
          Hashtbl.replace rule_table ~key:rname ~data;
          ()
        | _ -> ()
      end;
      [rname]
    | _ ->
      SemiPerm.gen_paramfixes prop_pds rpds
      |> List.map ~f:(fun pfs ->
        let inst_name = get_rule_inst_name rname pfs in
        begin
          match Hashtbl.find rule_table inst_name with
          | None ->
            let r = Hashtbl.find_exn raw_rule_table rname in
            let ri = apply_rule r ~p:pfs in
            let Rule(_, _, guard, statement) = ri in
            let guards = flat_and_to_list guard in
            let assigns = statement_2_assigns statement in
            let data = (ri, concrete_rule ri pfs, guards, assigns) in
            Hashtbl.replace rule_table ~key:inst_name ~data;
            ()
          | _ -> ()
        end;
        inst_name
      )
  )

let reorder_formList sour template =
  let rec wrapper sour template res =
    match template with
    | [] -> res
    | t::template' ->
      let rec find_in_sour sour others =
        match sour with
        | [] -> raise Empty_exception
        | s::sour' ->
          if ToStr.Debug.form_act t = ToStr.Debug.form_act s then
            s, others@sour'
          else
            find_in_sour sour' (others@[s])
      in
      let f, sour' = find_in_sour sour [] in
      wrapper sour' template' (res@[f])
  in
  ToStr.Debug.ignore_paramref := true;
  let res = wrapper sour template [] in
  ToStr.Debug.ignore_paramref := false;
  res

let fix_relations_with_cinvs cinvs relations =
  let pairs = List.map cinvs ~f:(fun cinv -> concrete_prop_2_form cinv, cinv) in
  if pairs = [] then () else begin
    print_endline (String.concat ~sep:"\n" (
      List.map pairs ~f:(fun (f, _) -> "NewInv: "^ToStr.Smv.form_act f)
    ))
  end;
  let rec wrapper relations res =
    match relations with
    | [] -> res
    | relation::relations' ->
      let fixed = 
        match relation with
        | {rule; inv; branch; relation=InvHoldForRule3(rel_cinv)} ->
          let ConcreteRule(_, pfs_rule) = rule in
          let ConcreteProp(_, pfs_prop) = inv in
          begin
            let rel_inv = concrete_prop_2_form rel_cinv in
            (* Rename parameters of the actual generated invariant to be
               consistent with the concrete rule and inv
            *)
            let renamed = RenameParam.form_act ~pfs_rule ~pfs_prop rel_inv in
            let ConcreteProp(Prop(_, ppds, pform), ppfs) =
              form_2_concreate_prop ~rename:false renamed
            in
            let rename_with_cinv (ConcreteProp(Prop(pname, _, cform), _)) =
              let reordered =
                match pform with
                | AndList(fl) ->
                  let AndList(template_inv) = cform in
                  andList (reorder_formList fl template_inv)
                | _ -> pform
              in
              let res = concrete_prop (prop pname ppds reordered) ppfs in
              let before = ToStr.Smv.form_act renamed in
              let after = ToStr.Smv.form_act (concrete_prop_2_form res) in
              if not (before = after) then Prt.info ("Reorder "^before^" to "^after) else ();
              res
            in
            match List.find pairs ~f:(fun (inv, _) -> symmetry_form inv rel_inv = 0) with
            | Some(_, cinv) ->
              {rule; inv; branch; relation = invHoldForRule3 (rename_with_cinv cinv)}
            | None ->
              Prt.warning ("Implied by old: "^ToStr.Smv.form_act rel_inv);
              {rule; inv; branch; relation = invHoldForRule3 (rename_with_cinv rel_cinv)}
          end
        | _ -> relation
      in
      wrapper relations' (res@[fixed])
  in
  List.map relations ~f:(fun rels -> List.map rels ~f:(fun rs -> wrapper rs []))

let get_res_of_cinv cinv rname_paraminfo_pairs =
  let (ConcreteProp(Prop(_, prop_pds, form), _)) = cinv in
  let vars_of_cinv = VarNames.of_form form in
  let rule_names = List.filter (Hashtbl.keys rule_vars_table) ~f:(fun rn ->
    String.Set.is_empty (String.Set.inter vars_of_cinv (Hashtbl.find_exn rule_vars_table rn))
  ) in
  let relations_of_hold2 = List.map rule_names ~f:(fun rn -> 
    [[deal_with_case_2 (all_rule_inst_from_name rn) cinv (form_2_concreate_prop chaos)]]
  ) in
  let rule_inst_names = 
    compute_rule_inst_names rname_paraminfo_pairs prop_pds
    |> List.filter ~f:(fun crns ->
      match crns with
      | [] -> raise Empty_exception
      | crn::_ -> all rule_names ~f:(fun n -> not (get_rname_of_crname crn = n)))
  in
  let crules = 
    List.map rule_inst_names ~f:(fun ns ->
      List.map ns ~f:(fun n ->
        match Hashtbl.find rule_table n with
        | None -> Prt.error n; raise Empty_exception
        | Some(cr) -> cr
      )
    )
  in
  let new_invs, new_relations =
    let invs, rels = List.unzip (List.map crules ~f:(fun r_insts ->
      List. unzip (List.map r_insts ~f:(fun r_inst ->
        List.unzip (tabular_expans r_inst ~cinv)
      ))
    )) in
    List.concat (List.concat (List.concat invs)), rels
  in
  let cinvs = InvLib.add_many new_invs in
  cinvs, fix_relations_with_cinvs cinvs new_relations@relations_of_hold2


let read_res_cache cinvs =
  let cinvs' = Storage.get (!protocol_name) "cinvs" cinvs (List.t_of_sexp concrete_prop_of_sexp) in
  let inv_cinv_pairs =
    let default = List.map cinvs ~f:(fun cinv -> Tuple2.create (concrete_prop_2_form cinv) cinv) in
    let convertor = List.t_of_sexp (Tuple2.t_of_sexp formula_of_sexp concrete_prop_of_sexp) in
    let tuple2s = Storage.get (!protocol_name) "invlib" default convertor in
    List.map tuple2s ~f:(fun t -> Tuple2.get1 t, Tuple2.get2 t)
  in
  let relations =
    let convertor = List.t_of_sexp (List.t_of_sexp (List.t_of_sexp t_of_sexp)) in
    Storage.get_many (!protocol_name) "relations" [] convertor
  in
  InvLib.pairs := inv_cinv_pairs;
  InvLib.index := (List.length inv_cinv_pairs + 1);
  (cinvs', relations)

let write_res_cache cinvs new_relations =
  let tuple2s = List.map (!InvLib.pairs) ~f:(fun (f, cinv) -> Tuple2.create f cinv) in
  let invlib_convertor = List.sexp_of_t (Tuple2.sexp_of_t sexp_of_formula sexp_of_concrete_prop) in
  let rel_convertor = List.sexp_of_t (List.sexp_of_t (List.sexp_of_t sexp_of_t)) in
  Storage.replace (!protocol_name) "cinvs" cinvs (List.sexp_of_t sexp_of_concrete_prop);
  Storage.replace (!protocol_name) "invlib" tuple2s invlib_convertor;
  Storage.add_many (!protocol_name) "relations" new_relations rel_convertor;;

(* This function has problems and is discarded *)
let upgrade_res_cache () =
  let eliminate_eqn_TF form =
    match form with
    | Neg(Eqn(Const(Boolc(true)), e1))
    | Neg(Eqn(e1, Const(Boolc(true)))) -> eqn e1 (Const(Boolc(false)))
    | Neg(Eqn(Const(Boolc(false)), e1))
    | Neg(Eqn(e1, Const(Boolc(false)))) -> eqn e1 (Const(Boolc(true)))
    | _ -> form
  in
  let cinvs = InvLib.get_all_cinvs () in
  let _, relations = read_res_cache [] in
  let cinvs' = List.map cinvs ~f:(fun cinv ->
    let ConcreteProp(Prop(pn, pds, f), pfs) = cinv in
    let cinv' = concrete_prop (prop pn pds (eliminate_eqn_TF f)) pfs in
    if not (cinv = cinv') then
      Prt.warning (ToStr.Smv.form_act (concrete_prop_2_form cinv'))
    else ();
    Tuple2.create (concrete_prop_2_form cinv') cinv'
  ) in
  let relations' = List.map relations ~f:(fun rels ->
    List.map rels ~f:(fun rs ->
      List.map rs ~f:(fun rlist ->
        List.map rlist ~f:(fun rel ->
          let {rule; inv; branch; relation} = rel in
          let ConcreteProp(Prop(pn, p_pds, p_form), p_pfs) = inv in
          let inv' = concrete_prop (prop pn p_pds (eliminate_eqn_TF p_form)) p_pfs in
          let ConcreteProp(Prop(bn, b_pds, b_form), b_pfs) = branch in
          let branch' = concrete_prop (prop bn b_pds (eliminate_eqn_TF b_form)) b_pfs in
          let relation' =
            match relation with
            | InvHoldForRule1
            | InvHoldForRule2 -> relation
            | InvHoldForRule3(ConcreteProp(Prop(cn, c_pds, c_form), c_pfs)) ->
              invHoldForRule3 (concrete_prop (prop cn c_pds (eliminate_eqn_TF c_form)) c_pfs)
          in
          {rule; inv=inv'; branch=branch'; relation=relation'}
        )
      )
    )
  ) in
  let invlib_convertor = List.sexp_of_t (Tuple2.sexp_of_t sexp_of_formula sexp_of_concrete_prop) in
  let rel_convertor = List.sexp_of_t (List.sexp_of_t (List.sexp_of_t sexp_of_t)) in
  Storage.replace (!protocol_name) "invlib" cinvs' invlib_convertor;
  Storage.replace_many (!protocol_name) "relations" relations' rel_convertor;;


(* Find new inv and relations with concrete rules and a concrete invariant *)
let tabular_rules_cinvs rname_paraminfo_pairs cinvs relations =
  let rec wrapper cinvs relations =
    match cinvs with
    | [] -> (InvLib.get_all_cinvs (), relations)
    | cinv::cinvs' ->
      let (new_cinvs, new_relations) = get_res_of_cinv cinv rname_paraminfo_pairs in
      let cinvs'' = cinvs'@new_cinvs in
      write_res_cache cinvs'' [new_relations];
      wrapper cinvs'' (relations@[new_relations])
  in
  wrapper cinvs relations



let simplify_prop property =
  let Prop(_, pds, f) = property in
  let orList_items =
    if List.length pds > 0 then
      let ps = cart_product_with_paramfix pds (!type_defs) in
      List.map ps ~f:(fun p -> simplify ~eli_eqn:true (neg (apply_form f ~p)))
    else begin
      [simplify ~eli_eqn:true (neg f)]
    end
  in
  orList_items
  |> List.map ~f:(fun form -> match form with | OrList(fl) -> fl | _ -> [form])
  |> List.concat
  |> List.filter ~f:(fun x -> match x with | Miracle -> false | _ -> true)
  |> stupid_dedup_list ~f:(fun x y -> symmetry_form x y = 0)




let check_invs_on_init cinvs init =
  let assigns = statement_2_assigns init in
  List.map cinvs ~f:(fun cinv ->
    let inv = concrete_prop_2_form cinv in
    cinv, List.filter assigns ~f:(fun assign ->
      let res = List.map (form_eval inv ~assigns:[assign]) ~f:(fun (g, f) -> andList [g; f]) in
      let has_false = List.exists res ~f:(fun f -> is_tautology f) in
      if has_false then
        raise (Invariant_not_sat_on_init(ToStr.Smv.form_act inv))
      else
        List.exists res ~f:(fun f -> is_tautology (neg f))
    )
    |> List.map ~f:(fun (v, _) -> VarNames.of_var v)
    |> String.Set.union_list
  )




let result_to_str (cinvs, relations) =
  let invs_str =
    cinvs
    |> List.map ~f:(fun cinv ->
      let ConcreteProp(Prop(name, _, _), _) = cinv in
      name^": "^ToStr.Smv.form_act (concrete_prop_2_form cinv)
    )
  in
  let relations_str = List.map relations ~f:to_str in
  String.concat ~sep:"\n" (relations_str@invs_str)

(** Find invs and causal relations of a protocol

    @param protocol the protocol
    @param prop_params property parameters given
    @return causal relation table
*)
let find ?(insym_types=[]) ?(smv_escape=(fun inv_str -> inv_str))
    ?(smv="") ?(smv_ord="") ?(smv_bmc="") ?(murphi="") protocol =
  let {name; types; vardefs; init; rules; properties} = Loach.Trans.act ~loach:protocol in
  let _smt_context = Smt.set_context name (ToStr.Smt2.context_of ~insym_types ~types ~vardefs) in
  let _mu_context = Murphi.set_context name murphi in
  (*let _smv_bmc_context =
    if smv_bmc = "" then
      SmvBmc.set_context name (Loach.ToSmv.protocol_act ~limit_param:false protocol)
    else begin SmvBmc.set_context name smv_bmc end
  in*)
  type_defs := types;
  protocol_name := name;
  cache_vars_of_rules rules;
  let init_cinvs =
    let invs =
      List.concat (List.map properties ~f:simplify_prop)
      |> List.map ~f:(normalize ~types:(!type_defs))
    in
    let indice = up_to (List.length invs) in
    List.map2_exn invs indice ~f:(fun f id -> form_2_concreate_prop ~id:(id + 1) f)
  in
  let cinvs, relations = read_res_cache init_cinvs in
  Prt.warning ("initial invs:\n"^String.concat ~sep:"\n" (
    List.map cinvs ~f:(fun cinv -> ToStr.Smv.form_act (concrete_prop_2_form cinv))
  ));
  let _smv_context =
    if List.is_empty cinvs then 0
    else begin
      if smv = "" then
        Smv.set_context ~escape:smv_escape name (Loach.ToSmv.protocol_act protocol) ~smv_ord
      else begin Smv.set_context ~escape:smv_escape name smv ~smv_ord end
    end
  in
  let get_rulename_param_pair r =
    let Paramecium.Rule(rname, paramdefs, _, _) = r in
    let ps = cart_product_with_paramfix paramdefs (!type_defs) in
    Hashtbl.replace raw_rule_table ~key:rname ~data:r;
    (rname, paramdefs)
  in
  let rname_paraminfo_pairs = List.map rules ~f:get_rulename_param_pair in
  let (cinvs, relations) = tabular_rules_cinvs rname_paraminfo_pairs cinvs relations in
  let cinvs_with_inits = check_invs_on_init cinvs init in
  printf "%s\n" (result_to_str (cinvs, List.concat (List.concat (List.concat (relations)))));
  (cinvs_with_inits, relations)
