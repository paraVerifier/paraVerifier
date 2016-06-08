
open Core.Std
open Utils
open Paramecium
open Loach







let spaces = ref 2

let gen_spaces () = String.make (!spaces) ' ' 

let const_act c =
  match c with
  | Intc(i) -> Int.to_string i
  | Strc(s) -> s
  | Boolc(b) -> Bool.to_string b






let type_act t = 
  let Enum(name, consts) = t in
  match consts with
  | c::_ ->
    begin
      match c with
      | Boolc(_) -> ""
      | Strc(_) ->
        let items_str = String.concat ~sep:", " (List.map consts ~f:const_act) in
        sprintf "%s%s : enum{%s};" (gen_spaces ()) name items_str
      | Intc(_) ->
        let c'::_ = List.rev consts in
        sprintf "%s%s : %s..%s;" (gen_spaces ()) name (const_act c) (const_act c')
    end
  | _ -> raise Empty_exception








type node =
  | Node of string * paramdef list * node list * string

let find_vdp vd_part ls =
  let (name, pds) = vd_part in
  let rec wrapper heads ls =
    match ls with
    | [] -> Node(name, pds, [], ""), heads
    | i::ls' ->
      let Node(name', _, _, _) = i in
      if name = name' then
        i, (heads@ls')
      else begin
        wrapper (heads@[i]) ls'
      end
  in
  wrapper [] ls

let build_vars_tree vardefs =
  let rec traverse cur_list ~cur_vd ~tname =
    match cur_vd with
    | [] -> cur_list
    | vd_part::cur_vd' ->
      let (Node(name, pds, next_ls, _)), cur_list = find_vdp vd_part cur_list in
      let next_ls = traverse next_ls ~cur_vd:cur_vd' ~tname in
      if cur_vd' = [] then
        (Node(name, pds, next_ls, tname))::cur_list
      else begin
        (Node(name, pds, next_ls, ""))::cur_list
      end
  in
  List.fold vardefs ~init:[] ~f:(fun res x ->
    let Arrdef(vd_parts, tname) = x in
    traverse res ~cur_vd:vd_parts ~tname
  )

let record_table = Hashtbl.create ~hashable:String.hashable ()

let get_type_id nodes =
  let names = List.map nodes ~f:(fun (Node(name, _, _, _)) -> name) in
  String.concat ~sep:"," (List.sort names ~cmp:String.compare)

let gen_var_str trees =
  let records = ref [] in
  let get_arr_of pds = String.concat ~sep:" " (
    List.map pds ~f:(fun (Paramdef(_, t)) -> sprintf "array [%s] of" t)
  ) in
  let rec wrapper tree =
    match tree with
    | Node(name, pds, [], tname) -> sprintf "%s : %s %s;" name (get_arr_of pds) tname
    | Node(name, pds, nodes, _) ->
      begin
        let key = get_type_id nodes in
        match Hashtbl.find record_table key with
        | Some(record_name) -> sprintf "%s : %s %s;" name (get_arr_of pds) record_name
        | None ->
          let sub_items = List.map nodes ~f:wrapper in
          let record_name = sprintf "record_%d" (Hashtbl.length record_table) in
          let record_body = String.concat ~sep:"\n" sub_items in
          let record_str = sprintf "%s : record\n%s\nend;" record_name record_body in
          records := (!records)@[record_str];
          Hashtbl.replace record_table ~key ~data:record_name;
          sprintf "%s : %s %s;" name (get_arr_of pds) record_name
      end
  in
  let vars = List.map trees ~f:wrapper in
  (!records), vars

let record_act vardefs =
  let trees = build_vars_tree vardefs in
  let record_defs, var_defs = gen_var_str trees in
  sprintf "%s\n\n\nvar\n%s" (String.concat ~sep:"\n\n\n" record_defs) (String.concat ~sep:"\n" var_defs)








let paramdef_act (Paramdef(vn, tn)) = sprintf "%s : %s" vn tn

let paramref_act pr =
  match pr with
  | Paramfix(_, _, c) -> const_act c
  | Paramref(name) -> name

let var_act v =
  let Arr(ls) = v in
  String.concat ~sep:"." (List.map ls ~f:(fun (n, prs) ->
    match prs with
    | [] -> n
    | _ ->
      let actual_ps = List.map prs ~f:paramref_act in
      sprintf "%s%s" n (String.concat (List.map actual_ps ~f:(fun p -> sprintf "[%s]" p)))
  ))

let rec exp_act exp =
  match exp with
  | Const(c) -> const_act c
  | Var(v) -> var_act v
  | Param(pr) -> paramref_act pr
  | Ite(f, e1, e2) ->
    sprintf "(%s ? %s : %s)" (form_act f) (exp_act e1) (exp_act e2)
  | UIF(n, el) -> sprintf "(%s)" (String.concat ~sep:n (List.map el ~f:exp_act))
and form_act form =
  match form with
  | Chaos -> "true"
  | Miracle -> "false"
  | UIP(n, el) -> sprintf "(%s)" (String.concat ~sep:n (List.map el ~f:exp_act))
  | Eqn(e1, e2) -> sprintf "(%s = %s)" (exp_act e1) (exp_act e2)
  | Neg(form) -> sprintf "(!%s)" (form_act form)
  | AndList(fl) ->
    List.map fl ~f:(form_act)
    |> reduce ~default:"true" ~f:(fun res x -> sprintf "%s & %s" res x)
    |> sprintf "(%s)"
  | OrList(fl) ->
    List.map fl ~f:(form_act)
    |> reduce ~default:"false" ~f:(fun res x -> sprintf "%s | %s" res x)
    |> sprintf "(%s)"
  | Imply(f1, f2) -> sprintf "(%s -> %s)" (form_act f1) (form_act f2)
  | ForallFormula(pds, f) ->
    let pds_str = String.concat ~sep:"; " (List.map pds ~f:paramdef_act) in
    sprintf "(forall %s do %s endforall)" pds_str (form_act f)
  | ExistFormula(pds, f) ->
    let pds_str = String.concat ~sep:"; " (List.map pds ~f:paramdef_act) in
    sprintf "(exists %s do %s endexists)" pds_str (form_act f)

let rec statement_act s =
  match s with
  | Assign(v, e) -> sprintf "%s%s := %s;" (gen_spaces ()) (var_act v) (exp_act e)
  | Parallel(ss) -> String.concat ~sep:"\n" (List.map ss ~f:statement_act)
  | IfStatement(f, s) ->
    spaces := (!spaces) + 2;
    let s_str = statement_act s in
    spaces := (!spaces) - 2;
    sprintf "%sif %s then\n%s\n%sendif;" (gen_spaces ()) (form_act f) s_str (gen_spaces ())
  | IfelseStatement(f, s1, s2) ->
    spaces := (!spaces) + 2;
    let s1_str = statement_act s1 in
    let s2_str = statement_act s2 in
    spaces := (!spaces) - 2;
    sprintf "%sif %s then\n%s\nelse\n%s\n%sendif;" (gen_spaces ()) (form_act f) s1_str s2_str (gen_spaces ())
  | ForStatement(s, pds) ->
    let pds_str = String.concat ~sep:"; " (List.map pds ~f:paramdef_act) in
    spaces := (!spaces) + 2;
    let s_str = statement_act s in
    spaces := (!spaces) - 2;
    sprintf "%sfor %s do\n%s\n%sendfor;" (gen_spaces ()) pds_str s_str (gen_spaces ())

let rule_act r =
  let Rule(name, pds, f, s) = r in
  if pds = [] then
    let guard = sprintf "%s%s ==>" (gen_spaces ()) (form_act f) in
    let statements = statement_act s in
    sprintf "rule \"%s\"\n%s\nbegin\n%s\nendrule;" name guard statements
  else begin
    spaces := (!spaces) + 2;
    let guard = sprintf "%s%s ==>" (gen_spaces ()) (form_act f) in
    let statements = statement_act s in
    spaces := (!spaces) - 2;
    let sp = gen_spaces () in
    let rstr =
      sprintf "%srule \"%s\"\n%s\n%sbegin\n%s\n%sendrule;" sp name guard sp statements sp
    in
    let pds_str = String.concat ~sep:"; " (List.map pds ~f:paramdef_act) in
    sprintf "ruleset %s do\n%s\nendruleset;" pds_str rstr
  end

let prop_act p =
  let Prop(name, pds, f) = p in
  if pds = [] then
    sprintf "invariant \"%s\"\n%s%s;" name (gen_spaces ()) (form_act f)
  else begin
    spaces := (!spaces) + 2;
    let fstr = sprintf "%s%s" (gen_spaces ()) (form_act f) in
    spaces := (!spaces) - 2;
    let pds_str = String.concat ~sep:"; " (List.map pds ~f:paramdef_act) in
    sprintf "ruleset %s do\n%sinvariant \"%s\"\n%s;\nendruleset;" pds_str (gen_spaces ()) name fstr
  end

let init_act init =
  sprintf "startstate\nbegin\n%s\nendstartstate;" (statement_act init)

let protocol_act protocol =
  let {name; types; vardefs; init; rules; properties} = protocol in
  let types_str = "type\n"^String.concat ~sep:"\n" (List.map types ~f:type_act) in
  let record_var_str = record_act vardefs in
  let init_str = init_act init in
  let rules_str = String.concat ~sep:"\n\n\n" (List.map rules ~f:rule_act) in
  let props_str = String.concat ~sep:"\n\n\n" (List.map properties ~f:prop_act) in
  String.concat ~sep:"\n\n\n" [types_str; record_var_str; init_str; rules_str; props_str]


