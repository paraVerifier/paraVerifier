
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _epsilon = strc "epsilon"
let _req_shared = strc "req_shared"
let _req_exclusive = strc "req_exclusive"
let _invalid = strc "invalid"
let _shared = strc "shared"
let _exclusive = strc "exclusive"
let _True = boolc true
let _False = boolc false

let types = [
  enum "channelType" [_epsilon; _req_shared; _req_exclusive];
  enum "cacheType" [_invalid; _shared; _exclusive];
  enum "client" (int_consts [1; 2; 3]);
  enum "boolean" [_True; _False];
]



let vardefs = List.concat [
  [arrdef [("home_exclusive_granted", [])] "boolean"];
  [arrdef [("home_current_command", [])] "channelType"];
  [arrdef [("home_current_client", [])] "client"];
  [arrdef [("cache", [paramdef "i0" "client"])] "cacheType"];
  [arrdef [("home_sharer_list", [paramdef "i1" "client"])] "boolean"]
]

let init = (parallel [(forStatement (parallel [(assign (arr [("cache", [paramref "i"])]) (const _invalid)); (assign (arr [("home_sharer_list", [paramref "i"])]) (const (boolc false)))]) [paramdef "i" "client"]); (assign (global "home_current_client") (param (paramfix "j" "client" (intc 1)))); (assign (global "home_current_command") (const _epsilon)); (assign (global "home_exclusive_granted") (const (boolc false)))])

let n_t1 =
  let name = "n_t1" in
  let params = [paramdef "i" "client"] in
  let formula = (andList [(eqn (var (global "home_current_command")) (const _epsilon)); (eqn (var (arr [("cache", [paramref "i"])])) (const _invalid))]) in
  let statement = (parallel [(assign (global "home_current_command") (const _req_shared)); (assign (global "home_current_client") (param (paramref "i")))]) in
  rule name params formula statement

let n_t2 =
  let name = "n_t2" in
  let params = [paramdef "i" "client"] in
  let formula = (andList [(eqn (var (global "home_current_command")) (const _epsilon)); (neg (eqn (var (arr [("cache", [paramref "i"])])) (const _exclusive)))]) in
  let statement = (parallel [(assign (global "home_current_command") (const _req_exclusive)); (assign (global "home_current_client") (param (paramref "i")))]) in
  rule name params formula statement

let n_t3 =
  let name = "n_t3" in
  let params = [paramdef "i" "client"] in
  let formula = (andList [(eqn (var (arr [("home_sharer_list", [paramref "i"])])) (const _True)); (eqn (var (global "home_current_command")) (const _req_exclusive))]) in
  let statement = (parallel [(assign (global "home_exclusive_granted") (const (boolc false))); (assign (arr [("cache", [paramref "i"])]) (const _invalid)); (assign (arr [("home_sharer_list", [paramref "i"])]) (const (boolc false)))]) in
  rule name params formula statement

let n_t4 =
  let name = "n_t4" in
  let params = [paramdef "i" "client"] in
  let formula = (andList [(andList [(eqn (var (arr [("home_sharer_list", [paramref "i"])])) (const _True)); (eqn (var (global "home_current_command")) (const _req_shared))]); (eqn (var (global "home_exclusive_granted")) (const _True))]) in
  let statement = (parallel [(assign (global "home_exclusive_granted") (const (boolc false))); (assign (arr [("cache", [paramref "i"])]) (const _shared)); (assign (arr [("home_sharer_list", [paramref "i"])]) (const (boolc true)))]) in
  rule name params formula statement

let n_t5 =
  let name = "n_t5" in
  let params = [paramdef "i" "client"] in
  let formula = (andList [(andList [(eqn (var (global "home_current_client")) (param (paramref "i"))); (eqn (var (global "home_current_command")) (const _req_shared))]); (eqn (var (global "home_exclusive_granted")) (const _False))]) in
  let statement = (parallel [(assign (global "home_current_command") (const _epsilon)); (assign (arr [("home_sharer_list", [paramref "i"])]) (const (boolc true))); (assign (arr [("cache", [paramref "i"])]) (const _shared))]) in
  rule name params formula statement

let n_t6 =
  let name = "n_t6" in
  let params = [paramdef "i" "client"] in
  let formula = (andList [(andList [(andList [(eqn (var (global "home_current_command")) (const _req_exclusive)); (eqn (var (global "home_exclusive_granted")) (const _False))]); (eqn (var (global "home_current_client")) (param (paramref "i")))]); (forallFormula [paramdef "c" "client"] (eqn (var (arr [("home_sharer_list", [paramref "c"])])) (const (boolc false))))]) in
  let statement = (parallel [(assign (global "home_current_command") (const _epsilon)); (assign (global "home_exclusive_granted") (const (boolc true))); (assign (arr [("home_sharer_list", [paramref "i"])]) (const (boolc true))); (assign (arr [("cache", [paramref "i"])]) (const _exclusive))]) in
  rule name params formula statement

let rules = [n_t1; n_t2; n_t3; n_t4; n_t5; n_t6]

let n_coherence =
  let name = "n_coherence" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("cache", [paramref "i"])])) (const _exclusive)) (neg (eqn (var (arr [("cache", [paramref "j"])])) (const _exclusive))))) in
  prop name params formula

let properties = [n_coherence]


let protocol = {
  name = "n_germanish";
  types;
  vardefs;
  init;
  rules;
  properties;
}

let () = run_with_cmdline (fun () ->
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol
    ~murphi:(In_channel.read_all "n_germanish.m")
  in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)

