
open Core.Std
open Utils
open Paramecium
open InvFinder
open ToStr



(*let hashtbl_keys h = Hashtbl.fold (fun key _ l -> key :: l) h []
let hashtbl_values h = Hashtbl.fold (fun _ value l -> value :: l) h []
let hashtbl2assoc_list h = Hashtbl.fold (fun key value l -> (key, value) :: l) h []
;;

let cenvNil = Hashtbl.create ~hashable:String.hashable ()*)

(*f is a special formula, which is a conjunction of eqs, e.g.,
v1=c1 & v2=c2 ..., where v1 v2 are values, and c1  c2 are values*)
let form2State form env=
  match form with
  | Eqn(Var(v), e) -> 
	let ()=Hashtbl.replace env ~key:(ToStr.Smv.var_act v) ~data:(v, e)in
             env
  | AndList eqs ->
    begin
      match eqs with
      | [] -> env
      | eq'::eqs' ->  
         let ()=
         (List.fold eqs ~init:() ~f:(fun remainded eq ->
          let  Eqn(Var(v), e) = eq in
          Hashtbl.replace env ~key:(ToStr.Smv.var_act v) ~data:(v, e))) in
        env         
    end

let assoc key value l = (key, value) :: l

let hashtbl2assoc_list h = Hashtbl.fold h ~init:[] ~f:(fun ~key ~data res ->
  let (v, e) = data in
  assoc v e res
)
  
let state2Form env =
  andList (List.map (hashtbl2assoc_list env) ~f:(fun (v, e) -> eqn (var v) e))

let printEnv env =
  Prt.info ("env: "^String.concat ~sep:", " (Hashtbl.keys env))

exception State_env_error
  
let rec expAct env  e =
  match e with
  | Const(c) -> e
  | Var(v) ->  
     begin
     match (Hashtbl.find  env (ToStr.Smv.var_act v) ) with
     |Some(p) -> snd( p)
     |None ->
       printEnv env;
       Prt.error (sprintf "Can't find %s in env" (ToStr.Smv.var_act v));
       raise State_env_error
     end
  | Param(pf) -> 
    (match pf with 
    |Paramfix(name,t,c) -> e
    |_ -> raise State_env_error)
    
  | Ite(f, e1,e2) ->
   begin 
   if (formAct  env f)
   then expAct env e1
   else expAct env e2
   end
  
and formAct env f =
  match f with
  | Chaos -> true
  | Miracle -> false
  | Eqn(e1, e2) ->  (expAct env e1)= (expAct env e2)
  | Neg(g) ->  not (formAct env g)
  | AndList(fl) ->
      List.fold   ~init:true ~f:(fun res x ->   res && (formAct env x)) fl
  | OrList(fl) ->
      List.fold  ~init:false ~f:(fun res x ->   res || (formAct env x)) fl
  | Imply(f1, f2) -> not (formAct env f1) || (formAct env f2)

let rec updateItemsGen env statement=
 match statement with
 |Assign(v,e) ->
  [(v, expAct env e)]
 |Parallel(sl) ->
   List.fold ~init:[] ~f:(fun res x ->     res @ (updateItemsGen env x)) sl
     

let updateState env statement=
  let items=updateItemsGen env statement in
  let s1=Hashtbl.copy env in
  let ()=List.fold items ~init:() 
  ~f:(fun remainded pair -> 
      let (v,e) = pair in Hashtbl.replace s1  ~key:(ToStr.Smv.var_act v) ~data:(v,e))
  in
   s1  

let fwdBfs inits rules bounds=
   let rec wrapper cur res =
    if List.length res >= bounds || List.is_empty cur then
      res
    else begin
      let c::cur' = cur in        
      let found = List.concat (List.map rules ~f:(fun (Rule(n, p, f, s)) ->
        let st=Hashtbl.create ~hashable:String.hashable () in  
      	let st1 = form2State c st in
        if (formAct st1 f) then  
          [state2Form (updateState st1 s)]
        else []
      ))   in
      let new_found = List.fold found ~init:[] ~f:(fun remained x ->
        match List.exists res ~f:(fun g ->  x= g) with
        | true -> remained
        | false -> remained@[x]
      ) in
      wrapper (cur'@new_found) (res@new_found)
    end 
in
  wrapper [inits] [inits]

