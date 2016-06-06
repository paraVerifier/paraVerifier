
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _op_invalid = strc "op_invalid"
let _read_shared = strc "read_shared"
let _read_exclusive = strc "read_exclusive"
let _req_upgrade = strc "req_upgrade"
let _invalidate = strc "invalidate"
let _invalidate_ack = strc "invalidate_ack"
let _grant_shared = strc "grant_shared"
let _grant_upgrade = strc "grant_upgrade"
let _grant_exclusive = strc "grant_exclusive"
let _req_read_shared = strc "req_read_shared"
let _req_read_exclusive = strc "req_read_exclusive"
let _req_req_upgrade = strc "req_req_upgrade"
let _cache_invalid = strc "cache_invalid"
let _cache_shared = strc "cache_shared"
let _cache_exclusive = strc "cache_exclusive"
let _inactive = strc "inactive"
let _pending = strc "pending"
let _completed = strc "completed"
let _True = boolc true
let _False = boolc false

let types = [
  enum "opcode" [_op_invalid; _read_shared; _read_exclusive; _req_upgrade; _invalidate; _invalidate_ack; _grant_shared; _grant_upgrade; _grant_exclusive];
  enum "request_opcode" [_req_read_shared; _req_read_exclusive; _req_req_upgrade];
  enum "cache_state" [_cache_invalid; _cache_shared; _cache_exclusive];
  enum "status_type" [_inactive; _pending; _completed];
  enum "addr_type" (int_consts [1; 2]);
  enum "num_data_type" (int_consts [1]);
  enum "node_id" (int_consts [0; 1; 2; 3]);
  enum "channel_id" (int_consts [1; 2; 3]);
  enum "boolean" [_True; _False];
]

let _data_type = List.concat [
  [arrdef [("values", [paramdef "i0" "num_data_type"])] "boolean"]
]

let _cache_record = List.concat [
  [arrdef [("state", [])] "cache_state"];
  record_def "data" [] _data_type
]

let _message_type = List.concat [
  [arrdef [("source", [])] "node_id"];
  [arrdef [("dest", [])] "node_id"];
  [arrdef [("op", [])] "opcode"];
  [arrdef [("addr", [])] "addr_type"];
  record_def "data" [] _data_type
]

let _message_buf_type = List.concat [
  record_def "msg" [] _message_type;
  [arrdef [("valid", [])] "boolean"]
]

let _addr_request_type = List.concat [
  [arrdef [("home", [])] "node_id"];
  [arrdef [("op", [])] "opcode"];
  record_def "data" [] _data_type;
  [arrdef [("status", [])] "status_type"]
]

let _home_request_type = List.concat [
  [arrdef [("source", [])] "node_id"];
  [arrdef [("op", [])] "opcode"];
  record_def "data" [] _data_type;
  [arrdef [("invalidate_list", [paramdef "i1" "node_id"])] "boolean"];
  [arrdef [("status", [])] "status_type"]
]

let _node_type = List.concat [
  record_def "memory" [paramdef "i2" "addr_type"] _data_type;
  record_def "cache" [paramdef "i3" "addr_type"] _cache_record;
  [arrdef [("directory", [paramdef "i4" "addr_type"; paramdef "i5" "node_id"])] "cache_state"];
  [arrdef [("local_requests", [paramdef "i6" "addr_type"])] "boolean"];
  record_def "home_requests" [paramdef "i7" "addr_type"] _home_request_type;
  record_def "remote_requests" [paramdef "i8" "addr_type"] _addr_request_type;
  record_def "inchan" [paramdef "i9" "channel_id"] _message_buf_type;
  record_def "outchan" [paramdef "i10" "channel_id"] _message_buf_type
]

let vardefs = List.concat [
  record_def "node" [paramdef "i11" "node_id"] _node_type;
  record_def "auxdata" [paramdef "i12" "addr_type"] _data_type
]

let init = (parallel [(forStatement (parallel [(forStatement (parallel [(forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("memory", [paramref "j"])]; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _cache_invalid)); (forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("directory", [paramref "j"; paramref "k"])]]) (const _cache_invalid)) [paramdef "k" "node_id"]); (assign (record [arr [("node", [paramref "i"])]; arr [("local_requests", [paramref "j"])]]) (const (boolc false))); (assign (record [arr [("node", [paramref "i"])]; arr [("home_requests", [paramref "j"])]; global "source"]) (const (intc 0))); (assign (record [arr [("node", [paramref "i"])]; arr [("home_requests", [paramref "j"])]; global "op"]) (const _op_invalid)); (forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("home_requests", [paramref "j"])]; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("home_requests", [paramref "j"])]; arr [("invalidate_list", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "node_id"]); (assign (record [arr [("node", [paramref "i"])]; arr [("home_requests", [paramref "j"])]; global "status"]) (const _inactive)); (assign (record [arr [("node", [paramref "i"])]; arr [("remote_requests", [paramref "j"])]; global "home"]) (const (intc 0))); (assign (record [arr [("node", [paramref "i"])]; arr [("remote_requests", [paramref "j"])]; global "op"]) (const _op_invalid)); (forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("remote_requests", [paramref "j"])]; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (assign (record [arr [("node", [paramref "i"])]; arr [("remote_requests", [paramref "j"])]; global "status"]) (const _inactive))]) [paramdef "j" "addr_type"]); (forStatement (parallel [(assign (record [arr [("node", [paramref "i"])]; arr [("inchan", [paramref "j"])]; global "msg"; global "source"]) (const (intc 0))); (assign (record [arr [("node", [paramref "i"])]; arr [("inchan", [paramref "j"])]; global "msg"; global "dest"]) (const (intc 0))); (assign (record [arr [("node", [paramref "i"])]; arr [("inchan", [paramref "j"])]; global "msg"; global "op"]) (const _op_invalid)); (assign (record [arr [("node", [paramref "i"])]; arr [("inchan", [paramref "j"])]; global "msg"; global "addr"]) (const (intc 1))); (forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("inchan", [paramref "j"])]; global "msg"; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (assign (record [arr [("node", [paramref "i"])]; arr [("inchan", [paramref "j"])]; global "valid"]) (const (boolc false))); (assign (record [arr [("node", [paramref "i"])]; arr [("outchan", [paramref "j"])]; global "msg"; global "source"]) (const (intc 0))); (assign (record [arr [("node", [paramref "i"])]; arr [("outchan", [paramref "j"])]; global "msg"; global "dest"]) (const (intc 0))); (assign (record [arr [("node", [paramref "i"])]; arr [("outchan", [paramref "j"])]; global "msg"; global "op"]) (const _op_invalid)); (assign (record [arr [("node", [paramref "i"])]; arr [("outchan", [paramref "j"])]; global "msg"; global "addr"]) (const (intc 1))); (forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("outchan", [paramref "j"])]; global "msg"; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (assign (record [arr [("node", [paramref "i"])]; arr [("outchan", [paramref "j"])]; global "valid"]) (const (boolc false)))]) [paramdef "j" "channel_id"])]) [paramdef "i" "node_id"]); (forStatement (forStatement (assign (record [arr [("auxdata", [paramref "i"])]; arr [("values", [paramref "j"])]]) (const (boolc false))) [paramdef "j" "num_data_type"]) [paramdef "i" "addr_type"])])

let n_Transfer_message_from_source_via_ch =
  let name = "n_Transfer_message_from_source_via_ch" in
  let params = [paramdef "source" "node_id"; paramdef "ch" "channel_id"; paramdef "dest" "node_id"] in
  let formula = (andList [(andList [(eqn (param (paramref "dest")) (var (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "dest"]))); (eqn (var (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "valid"])) (const _True))]); (eqn (var (record [arr [("node", [paramref "dest"])]; arr [("inchan", [paramref "ch"])]; global "valid"])) (const _False))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "dest"])]; arr [("inchan", [paramref "ch"])]; global "msg"; global "source"]) (var (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "source"]))); (assign (record [arr [("node", [paramref "dest"])]; arr [("inchan", [paramref "ch"])]; global "msg"; global "dest"]) (var (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "dest"]))); (assign (record [arr [("node", [paramref "dest"])]; arr [("inchan", [paramref "ch"])]; global "msg"; global "op"]) (var (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "op"]))); (assign (record [arr [("node", [paramref "dest"])]; arr [("inchan", [paramref "ch"])]; global "msg"; global "addr"]) (var (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "addr"]))); (forStatement (assign (record [arr [("node", [paramref "dest"])]; arr [("inchan", [paramref "ch"])]; global "msg"; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "data"; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"]); (assign (record [arr [("node", [paramref "dest"])]; arr [("inchan", [paramref "ch"])]; global "valid"]) (var (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "valid"]))); (assign (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "source"]) (const (intc 0))); (assign (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "dest"]) (const (intc 0))); (assign (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "op"]) (const _op_invalid)); (assign (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "addr"]) (const (intc 1))); (forStatement (assign (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "msg"; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (assign (record [arr [("node", [paramref "source"])]; arr [("outchan", [paramref "ch"])]; global "valid"]) (const (boolc false)))]) in
  rule name params formula statement

let n_client_generates_new_req_for_addr =
  let name = "n_client_generates_new_req_for_addr" in
  let params = [paramdef "client" "node_id"; paramdef "req" "request_opcode"; paramdef "addr" "addr_type"; paramdef "channel1" "channel_id"] in
  let formula = (andList [(andList [(andList [(eqn (param (paramref "channel1")) (const (intc 1))); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("local_requests", [paramref "addr"])]])) (const _False))]); (orList [(orList [(andList [(eqn (param (paramref "req")) (const _req_read_shared)); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "state"])) (const _cache_invalid))]); (andList [(eqn (param (paramref "req")) (const _req_read_exclusive)); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "state"])) (const _cache_invalid))])]); (andList [(eqn (param (paramref "req")) (const _req_req_upgrade)); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "state"])) (const _cache_shared))])])]); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel1"])]; global "valid"])) (const _False))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel1"])]; global "msg"; global "source"]) (param (paramref "client"))); (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel1"])]; global "msg"; global "dest"]) (const (intc 0))); (ifelseStatement (eqn (param (paramref "req")) (const _req_read_shared)) (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel1"])]; global "msg"; global "op"]) (const _read_shared)) (ifelseStatement (eqn (param (paramref "req")) (const _req_read_exclusive)) (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel1"])]; global "msg"; global "op"]) (const _read_exclusive)) (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel1"])]; global "msg"; global "op"]) (const _req_upgrade)))); (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel1"])]; global "msg"; global "addr"]) (param (paramref "addr"))); (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel1"])]; global "valid"]) (const (boolc true))); (assign (record [arr [("node", [paramref "client"])]; arr [("local_requests", [paramref "addr"])]]) (const (boolc true)))]) in
  rule name params formula statement

let n_client_accepts_invalidate_request =
  let name = "n_client_accepts_invalidate_request" in
  let params = [paramdef "client" "node_id"; paramdef "addr" "addr_type"; paramdef "channel2" "channel_id"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (param (paramref "channel2")) (const (intc 2))); (eqn (param (paramref "addr")) (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "addr"])))]); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "valid"])) (const _True))]); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "op"])) (const _invalidate))]); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "status"])) (const _inactive))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "home"]) (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "source"]))); (assign (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "op"]) (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "op"]))); (assign (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "status"]) (const _pending)); (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "source"]) (const (intc 0))); (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "dest"]) (const (intc 0))); (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "op"]) (const _op_invalid)); (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "addr"]) (const (intc 1))); (forStatement (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "valid"]) (const (boolc false)))]) in
  rule name params formula statement

let n_client_processes_invalidate_request_for_addr =
  let name = "n_client_processes_invalidate_request_for_addr" in
  let params = [paramdef "client" "node_id"; paramdef "addr" "addr_type"] in
  let formula = (andList [(eqn (var (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "status"])) (const _pending)); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "op"])) (const _invalidate))]) in
  let statement = (parallel [(forStatement (assign (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"]); (assign (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "status"]) (const _completed)); (assign (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "state"]) (const _cache_invalid)); (forStatement (assign (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"])]) in
  rule name params formula statement

let n_client_prepares_invalidate_ack_for_addr =
  let name = "n_client_prepares_invalidate_ack_for_addr" in
  let params = [paramdef "client" "node_id"; paramdef "addr" "addr_type"; paramdef "channel3" "channel_id"] in
  let formula = (andList [(andList [(andList [(eqn (param (paramref "channel3")) (const (intc 3))); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "status"])) (const _completed))]); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "op"])) (const _invalidate))]); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel3"])]; global "valid"])) (const _False))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel3"])]; global "msg"; global "op"]) (const _invalidate_ack)); (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel3"])]; global "msg"; global "source"]) (param (paramref "client"))); (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel3"])]; global "msg"; global "dest"]) (var (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "home"]))); (forStatement (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel3"])]; global "msg"; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"]); (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel3"])]; global "msg"; global "addr"]) (param (paramref "addr"))); (assign (record [arr [("node", [paramref "client"])]; arr [("outchan", [paramref "channel3"])]; global "valid"]) (const (boolc true))); (assign (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "home"]) (const (intc 0))); (assign (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "op"]) (const _op_invalid)); (forStatement (assign (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (assign (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "status"]) (const _inactive))]) in
  rule name params formula statement

let n_client_receives_reply_from_home =
  let name = "n_client_receives_reply_from_home" in
  let params = [paramdef "client" "node_id"; paramdef "addr" "addr_type"; paramdef "channel2" "channel_id"] in
  let formula = (andList [(andList [(andList [(eqn (param (paramref "channel2")) (const (intc 2))); (eqn (param (paramref "addr")) (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "addr"])))]); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "valid"])) (const _True))]); (orList [(orList [(eqn (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "op"])) (const _grant_shared)); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "op"])) (const _grant_upgrade))]); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "op"])) (const _grant_exclusive))])]) in
  let statement = (parallel [(ifelseStatement (eqn (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "op"])) (const _grant_shared)) (parallel [(forStatement (assign (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "data"; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"]); (assign (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "state"]) (const _cache_shared))]) (ifelseStatement (eqn (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "op"])) (const _grant_upgrade)) (assign (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "state"]) (const _cache_exclusive)) (ifStatement (eqn (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "op"])) (const _grant_exclusive)) (parallel [(forStatement (assign (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "data"; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"]); (assign (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "state"]) (const _cache_exclusive))])))); (assign (record [arr [("node", [paramref "client"])]; arr [("local_requests", [paramref "addr"])]]) (const (boolc false))); (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "source"]) (const (intc 0))); (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "dest"]) (const (intc 0))); (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "op"]) (const _op_invalid)); (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "addr"]) (const (intc 1))); (forStatement (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "msg"; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (assign (record [arr [("node", [paramref "client"])]; arr [("inchan", [paramref "channel2"])]; global "valid"]) (const (boolc false)))]) in
  rule name params formula statement

let n_client_stores_data_in_cache_for_addr =
  let name = "n_client_stores_data_in_cache_for_addr" in
  let params = [paramdef "client" "node_id"; paramdef "addr" "addr_type"; paramdef "data" "boolean"; paramdef "data_n" "num_data_type"] in
  let formula = (andList [(neg (eqn (var (record [arr [("node", [paramref "client"])]; arr [("remote_requests", [paramref "addr"])]; global "status"])) (const _pending))); (eqn (var (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "state"])) (const _cache_exclusive))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "data"; arr [("values", [paramref "data_n"])]]) (param (paramref "data"))); (assign (record [arr [("auxdata", [paramref "addr"])]; arr [("values", [paramref "data_n"])]]) (param (paramref "data")))]) in
  rule name params formula statement

let n_home_accepts_a_request_message =
  let name = "n_home_accepts_a_request_message" in
  let params = [paramdef "home" "node_id"; paramdef "addr" "addr_type"; paramdef "source" "node_id"; paramdef "channel1" "channel_id"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (param (paramref "channel1")) (const (intc 1))); (eqn (param (paramref "addr")) (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "addr"])))]); (eqn (param (paramref "source")) (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "source"])))]); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "valid"])) (const _True))]); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"])) (const _inactive))]) in
  let statement = (parallel [(ifStatement (andList [(eqn (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "op"])) (const _req_upgrade)); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "source"])]])) (const _cache_invalid))]) (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "op"]) (const _read_exclusive))); (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "source"]) (param (paramref "source"))); (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "op"]) (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "op"]))); (ifelseStatement (andList [(eqn (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "op"])) (const _read_shared)); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "home"])]])) (const _cache_shared))]) (parallel [(ifelseStatement (eqn (var (record [arr [("node", [paramref "home"])]; arr [("cache", [paramref "addr"])]; global "state"])) (const _cache_shared)) (forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "home"])]; arr [("cache", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"]) (forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "home"])]; arr [("memory", [paramref "addr"])]; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"])); (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _completed))]) (ifelseStatement (andList [(andList [(eqn (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "op"])) (const _read_shared)); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "home"])]])) (const _cache_invalid))]); (neg (existFormula [paramdef "n" "node_id"] (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "n"])]])) (const _cache_exclusive))))]) (parallel [(forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "home"])]; arr [("memory", [paramref "addr"])]; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"]); (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _completed))]) (ifelseStatement (andList [(eqn (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "op"])) (const _read_shared)); (existFormula [paramdef "n" "node_id"] (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "n"])]])) (const _cache_exclusive)))]) (parallel [(forStatement (ifelseStatement (neg (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "n"])]])) (const _cache_invalid))) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; arr [("invalidate_list", [paramref "n"])]]) (const (boolc true))) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; arr [("invalidate_list", [paramref "n"])]]) (const (boolc false)))) [paramdef "n" "node_id"]); (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _pending))]) (ifelseStatement (eqn (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "op"])) (const _req_upgrade)) (parallel [(forStatement (ifelseStatement (andList [(neg (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "n"])]])) (const _cache_invalid))); (neg (eqn (param (paramref "n")) (param (paramref "source"))))]) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; arr [("invalidate_list", [paramref "n"])]]) (const (boolc true))) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; arr [("invalidate_list", [paramref "n"])]]) (const (boolc false)))) [paramdef "n" "node_id"]); (ifelseStatement (existFormula [paramdef "n" "node_id"] (andList [(neg (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "n"])]])) (const _cache_invalid))); (neg (eqn (param (paramref "n")) (param (paramref "source"))))])) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _pending)) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _completed)))]) (ifStatement (eqn (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "op"])) (const _read_exclusive)) (parallel [(forStatement (ifelseStatement (neg (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "n"])]])) (const _cache_invalid))) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; arr [("invalidate_list", [paramref "n"])]]) (const (boolc true))) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; arr [("invalidate_list", [paramref "n"])]]) (const (boolc false)))) [paramdef "n" "node_id"]); (ifelseStatement (existFormula [paramdef "n" "node_id"] (neg (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "n"])]])) (const _cache_invalid)))) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _pending)) (parallel [(forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "home"])]; arr [("memory", [paramref "addr"])]; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"]); (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _completed))]))])))))); (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "source"]) (const (intc 0))); (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "dest"]) (const (intc 0))); (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "op"]) (const _op_invalid)); (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "addr"]) (const (intc 1))); (forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "msg"; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel1"])]; global "valid"]) (const (boolc false)))]) in
  rule name params formula statement

let n_home_prepares_invalidate_for_addr =
  let name = "n_home_prepares_invalidate_for_addr" in
  let params = [paramdef "home" "node_id"; paramdef "addr" "addr_type"; paramdef "dest" "node_id"; paramdef "channel2" "channel_id"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (param (paramref "channel2")) (const (intc 2))); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; arr [("invalidate_list", [paramref "dest"])]])) (const _True))]); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"])) (const _pending))]); (existFormula [paramdef "n" "node_id"] (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; arr [("invalidate_list", [paramref "n"])]])) (const _True)))]); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "valid"])) (const _False))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "addr"]) (param (paramref "addr"))); (assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "op"]) (const _invalidate)); (assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "source"]) (param (paramref "home"))); (assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "dest"]) (param (paramref "dest"))); (assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "valid"]) (const (boolc true))); (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; arr [("invalidate_list", [paramref "dest"])]]) (const (boolc false)))]) in
  rule name params formula statement

let n_home_processes_invalidate_ack =
  let name = "n_home_processes_invalidate_ack" in
  let params = [paramdef "home" "node_id"; paramdef "addr" "addr_type"; paramdef "source" "node_id"; paramdef "channel3" "channel_id"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (param (paramref "channel3")) (const (intc 3))); (eqn (param (paramref "addr")) (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "msg"; global "addr"])))]); (eqn (param (paramref "source")) (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "msg"; global "source"])))]); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "valid"])) (const _True))]); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"])) (const _pending))]); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "msg"; global "op"])) (const _invalidate_ack))]) in
  let statement = (parallel [(ifStatement (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "source"])]])) (const _cache_exclusive)) (forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("memory", [paramref "addr"])]; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "msg"; global "data"; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"])); (forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "msg"; global "data"; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"]); (assign (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "source"])]]) (const _cache_invalid)); (ifelseStatement (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "op"])) (const _read_shared)) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _completed)) (ifelseStatement (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "op"])) (const _req_upgrade)) (ifStatement (forallFormula [paramdef "n" "node_id"] (imply (neg (eqn (param (paramref "n")) (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "source"])))) (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "n"])]])) (const _cache_invalid)))) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _completed))) (ifStatement (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "op"])) (const _read_exclusive)) (ifStatement (forallFormula [paramdef "n" "node_id"] (eqn (var (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "n"])]])) (const _cache_invalid))) (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _completed)))))); (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "msg"; global "source"]) (const (intc 0))); (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "msg"; global "dest"]) (const (intc 0))); (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "msg"; global "op"]) (const _op_invalid)); (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "msg"; global "addr"]) (const (intc 1))); (forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "msg"; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (assign (record [arr [("node", [paramref "home"])]; arr [("inchan", [paramref "channel3"])]; global "valid"]) (const (boolc false)))]) in
  rule name params formula statement

let n_home_sends_grant_for_addr =
  let name = "n_home_sends_grant_for_addr" in
  let params = [paramdef "home" "node_id"; paramdef "addr" "addr_type"; paramdef "source" "node_id"; paramdef "channel2" "channel_id"] in
  let formula = (andList [(andList [(andList [(eqn (param (paramref "channel2")) (const (intc 2))); (eqn (param (paramref "source")) (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "source"])))]); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"])) (const _completed))]); (eqn (var (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "valid"])) (const _False))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "source"]) (param (paramref "home"))); (assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "dest"]) (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "source"]))); (ifelseStatement (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "op"])) (const _read_shared)) (parallel [(assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "op"]) (const _grant_shared)); (assign (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "source"])]]) (const _cache_shared))]) (ifelseStatement (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "op"])) (const _req_upgrade)) (parallel [(assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "op"]) (const _grant_upgrade)); (assign (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "source"])]]) (const _cache_exclusive))]) (ifStatement (eqn (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "op"])) (const _read_exclusive)) (parallel [(assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "op"]) (const _grant_exclusive)); (assign (record [arr [("node", [paramref "home"])]; arr [("directory", [paramref "addr"; paramref "source"])]]) (const _cache_exclusive))])))); (forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "data"; arr [("values", [paramref "i"])]]) (var (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "data"; arr [("values", [paramref "i"])]]))) [paramdef "i" "num_data_type"]); (assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "msg"; global "addr"]) (param (paramref "addr"))); (assign (record [arr [("node", [paramref "home"])]; arr [("outchan", [paramref "channel2"])]; global "valid"]) (const (boolc true))); (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "source"]) (const (intc 0))); (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "op"]) (const _op_invalid)); (forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "data"; arr [("values", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "num_data_type"]); (forStatement (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; arr [("invalidate_list", [paramref "k"])]]) (const (boolc false))) [paramdef "k" "node_id"]); (assign (record [arr [("node", [paramref "home"])]; arr [("home_requests", [paramref "addr"])]; global "status"]) (const _inactive))]) in
  rule name params formula statement

let rules = [n_Transfer_message_from_source_via_ch; n_client_generates_new_req_for_addr; n_client_accepts_invalidate_request; n_client_processes_invalidate_request_for_addr; n_client_prepares_invalidate_ack_for_addr; n_client_receives_reply_from_home; n_client_stores_data_in_cache_for_addr; n_home_accepts_a_request_message; n_home_prepares_invalidate_for_addr; n_home_processes_invalidate_ack; n_home_sends_grant_for_addr]

let n_coherent =
  let name = "n_coherent" in
  let params = [paramdef "n1" "node_id"; paramdef "n2" "node_id"; paramdef "addr" "addr_type"] in
  let formula = (imply (andList [(neg (eqn (param (paramref "n1")) (param (paramref "n2")))); (eqn (var (record [arr [("node", [paramref "n1"])]; arr [("cache", [paramref "addr"])]; global "state"])) (const _cache_exclusive))]) (eqn (var (record [arr [("node", [paramref "n2"])]; arr [("cache", [paramref "addr"])]; global "state"])) (const _cache_invalid))) in
  prop name params formula

let n_data_consistency_property =
  let name = "n_data_consistency_property" in
  let params = [paramdef "client" "node_id"; paramdef "addr" "addr_type"; paramdef "d" "num_data_type"] in
  let formula = (imply (neg (eqn (var (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "state"])) (const _cache_invalid))) (eqn (var (record [arr [("node", [paramref "client"])]; arr [("cache", [paramref "addr"])]; global "data"; arr [("values", [paramref "d"])]])) (var (record [arr [("auxdata", [paramref "addr"])]; arr [("values", [paramref "d"])]])))) in
  prop name params formula

let properties = [n_coherent; n_data_consistency_property]


let protocol = {
  name = "n_german2004";
  types;
  vardefs;
  init;
  rules;
  properties;
}


let () = run_with_cmdline (fun () ->
  let insym_types = ["channel_id"; "boolean"; "request_opcode"] in
  let protocol = PartParam.apply_protocol insym_types protocol in
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol
    ~insym_types
    ~murphi:(In_channel.read_all "german2004.after.m")
    ~smv:(In_channel.read_all "german2k4n.smv")
    ~smv_ord:(In_channel.read_all "german2k4n.ord")
    ~smv_escape:(fun inv_str ->
      let replace s d =
        Re2.Regex.rewrite_exn (Re2.Regex.of_string s) ~template:d
      in
      inv_str
      |> replace "node\\[0\\].directory\\[1\\]" "directory"
      |> replace "node\\[0\\].memory\\[1\\].values\\[1\\]" "memory"
      |> replace "auxdata\\[1\\].values\\[1\\]" "auxdata"
      |> replace "node" "Node"
      |> replace "cache\\[1\\]" "cache"
      |> replace "data.values\\[1\\]" "data"
      |> replace "local_requests\\[1\\]" "local_requests"
      |> replace "remote_requests\\[1\\]" "remote_requests"
      |> replace "home_requests\\[1\\]" "home_requests"
      |> replace "chan_1" "chan1"
      |> replace "chan_2" "chan2"
      |> replace "chan_3" "chan3"
    )
  in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)

(*
let insym_types = ["channel_id"; "boolean"; "request_opcode"] in
let protocol = PartParam.apply_protocol insym_types protocol in
printf "%s\n\n\n" (ToMurphi.protocol_act protocol);;
*)

