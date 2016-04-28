(** Client for connect to smv/smt2 server
*)

open Core.Std;;
open Utils;;

exception Server_exception

type request_type =
  | ERROR
  | WAITING
  | OK
  | COMPUTE_REACHABLE
  | QUERY_REACHABLE
  | CHECK_INV
  | SMV_QUIT
  | GO_BMC
  | CHECK_INV_BMC
  | SMV_BMC_QUIT
  | SET_SMT2_CONTEXT
  | QUERY_SMT2
  | QUERY_STAND_SMT2
  | SET_MU_CONTEXT
  | CHECK_INV_BY_MU

let request_type_to_str rt =
  match rt with
  | ERROR -> "-2"
  | WAITING -> "-1"
  | OK -> "0"
  | COMPUTE_REACHABLE -> "1"
  | QUERY_REACHABLE -> "2"
  | CHECK_INV -> "3"
  | SMV_QUIT -> "7"
  | GO_BMC -> "10"
  | CHECK_INV_BMC -> "11"
  | SMV_BMC_QUIT -> "12"
  | SET_SMT2_CONTEXT -> "4"
  | QUERY_SMT2 -> "5"
  | QUERY_STAND_SMT2 -> "6"
  | SET_MU_CONTEXT -> "8"
  | CHECK_INV_BY_MU -> "9"

let str_to_request_type str =
  match str with
  | "-2" -> ERROR
  | "-1" -> WAITING
  | "0" -> OK
  | "1" -> COMPUTE_REACHABLE
  | "2" -> QUERY_REACHABLE
  | "3" -> CHECK_INV
  | "7" -> SMV_QUIT
  | "10" -> GO_BMC
  | "11" -> CHECK_INV_BMC
  | "12" -> SMV_BMC_QUIT
  | "4" -> SET_SMT2_CONTEXT
  | "5" -> QUERY_SMT2
  | "6" -> QUERY_STAND_SMT2
  | "8" -> SET_MU_CONTEXT
  | "9" -> CHECK_INV_BY_MU
  | _ -> Prt.error str; raise Empty_exception

let make_request str host port =
  let sock = Unix.socket ~domain:UnixLabels.PF_INET ~kind:UnixLabels.SOCK_STREAM ~protocol:0 in
  let res = String.make 1024 '\000' in
  Unix.connect sock ~addr:(UnixLabels.ADDR_INET(host, port));
  let _writed = Unix.write sock ~buf:str in
  let len = Unix.read sock ~buf:res in
  Unix.close sock;
  String.sub res ~pos:0 ~len

let command_id = ref 0

let request cmd req_str host port =
  let cmd  = request_type_to_str cmd in
  let cmd_id = !command_id in
  let req = sprintf "%s,%d,%s" cmd cmd_id req_str in
  let wrapped = sprintf "%d,%s" (String.length req) req in
  incr command_id; (*printf "%d\n" (!command_id);*)
  let res = String.split (make_request wrapped host port) ~on:',' in
  match res with
  | [] -> raise Empty_exception
  | status::res' -> 
    let s = str_to_request_type status in
    if s = ERROR then raise Server_exception
    else begin (s, res') end




module Smv = struct

  exception Cannot_check

  let host = ref (UnixLabels.inet_addr_of_string "127.0.0.1")

  let port = ref 50008
  
  let compute_reachable name content =
    let (status, _) = request COMPUTE_REACHABLE (sprintf "%s,%s" name content) (!host) (!port) in
    status = OK

  let query_reachable name =
    let (status, diameter) = request QUERY_REACHABLE name (!host) (!port) in
    if status = OK then 
      match diameter with
      | "-1"::[] -> raise Server_exception
      | d::[] -> Int.of_string d
      | _ -> raise Server_exception
    else begin 0 end

  let check_inv name inv =
    let (status, res) = request CHECK_INV (sprintf "%s,%s" name inv) (!host) (!port) in
    if status = OK then
      match res with
      | "0"::[] -> raise Cannot_check
      | r::[] -> Bool.of_string r
      | _ -> raise Server_exception
    else begin raise Server_exception end

  let quit name =
    let (s, _) = request SMV_QUIT name (!host) (!port) in
    s = OK

end


module SmvBMC = struct

  exception Cannot_check

  let host = ref (UnixLabels.inet_addr_of_string "127.0.0.1")

  let port = ref 50008
  
  let go_bmc name content =
    let (status, _) = request GO_BMC (sprintf "%s,%s" name content) (!host) (!port) in
    status = OK

  let check_inv name inv =
    let (status, res) = request CHECK_INV_BMC (sprintf "%s,%s" name inv) (!host) (!port) in
    if status = OK then
      match res with
      | "0"::[] -> raise Cannot_check
      | r::[] -> Bool.of_string r
      | _ -> raise Server_exception
    else begin raise Server_exception end

  let quit name =
    let (s, _) = request SMV_BMC_QUIT name (!host) (!port) in
    s = OK

end




module Murphi = struct

  let host = ref (UnixLabels.inet_addr_of_string "127.0.0.1")

  let port = ref 50008

  let set_context name context =
    let (s, _) = request SET_MU_CONTEXT (sprintf "%s,%s" name context) (!host) (!port) in
    s = OK

  let check_inv name inv =
    let (_, res) = request CHECK_INV_BY_MU (sprintf "%s,%s" name inv) (!host) (!port) in
    match res with
    | r::[] -> Bool.of_string r
    | _ -> raise Server_exception

end






module Smt2 = struct

let host = ref (UnixLabels.inet_addr_of_string "127.0.0.1")

let port = ref 50008

  let set_context name context =
    let (s, _) = request SET_SMT2_CONTEXT (sprintf "%s,%s" name context) (!host) (!port) in
    s = OK

  let check name f =
    let (_, res) = request QUERY_SMT2 (sprintf "%s,%s" name f) (!host) (!port) in
    match res with
    | r::[] ->
      if r = "unsat" then false
      else if r = "sat" then true
      else raise Server_exception
    | _ -> raise Server_exception

  let check_stand context f =
    let (_, res) = request QUERY_STAND_SMT2 (sprintf "%s,%s" context f) (!host) (!port) in
    match res with
    | r::[] -> 
      if r = "unsat" then false
      else if r = "sat" then true
      else raise Server_exception
    | _ -> raise Server_exception

end

