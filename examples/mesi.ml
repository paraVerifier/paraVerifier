
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _M = strc "M"
let _E = strc "E"
let _S = strc "S"
let _I = strc "I"
let _True = boolc true
let _False = boolc false

let types = [
  enum "location" [_M; _E; _S; _I];
  enum "client" (int_consts [1; 2; 3]);
  enum "boolean" [_True; _False];
]



let vardefs = List.concat [
  [arrdef [("state", [paramdef "i0" "client"])] "location"]
]

let init = (forStatement (assign (arr [("state", [paramref "i"])]) (const _I)) [paramdef "i" "client"])

let n_t1 =
  let name = "n_t1" in
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("state", [paramref "i"])])) (const _E)) in
  let statement = (assign (arr [("state", [paramref "i"])]) (const _M)) in
  rule name params formula statement

let n_t2 =
  let name = "n_t2" in
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("state", [paramref "i"])])) (const _I)) in
  let statement = (forStatement (ifelseStatement (eqn (param (paramref "j")) (param (paramref "i"))) (assign (arr [("state", [paramref "j"])]) (const _S)) (ifelseStatement (eqn (var (arr [("state", [paramref "j"])])) (const _E)) (assign (arr [("state", [paramref "j"])]) (const _S)) (ifelseStatement (eqn (var (arr [("state", [paramref "j"])])) (const _M)) (assign (arr [("state", [paramref "j"])]) (const _S)) (ifelseStatement (eqn (var (arr [("state", [paramref "j"])])) (const _I)) (assign (arr [("state", [paramref "j"])]) (const _I)) (assign (arr [("state", [paramref "j"])]) (const _S)))))) [paramdef "j" "client"]) in
  rule name params formula statement

let n_t3 =
  let name = "n_t3" in
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("state", [paramref "i"])])) (const _S)) in
  let statement = (forStatement (ifelseStatement (eqn (param (paramref "j")) (param (paramref "i"))) (assign (arr [("state", [paramref "j"])]) (const _E)) (assign (arr [("state", [paramref "j"])]) (const _I))) [paramdef "j" "client"]) in
  rule name params formula statement

let n_t4 =
  let name = "n_t4" in
  let params = [paramdef "i" "client"] in
  let formula = (eqn (var (arr [("state", [paramref "i"])])) (const _I)) in
  let statement = (forStatement (ifelseStatement (eqn (param (paramref "j")) (param (paramref "i"))) (assign (arr [("state", [paramref "j"])]) (const _E)) (assign (arr [("state", [paramref "j"])]) (const _I))) [paramdef "j" "client"]) in
  rule name params formula statement

let rules = [n_t1; n_t2; n_t3; n_t4]

let n_coherence =
  let name = "n_coherence" in
  let params = [paramdef "i" "client"; paramdef "j" "client"] in
  let formula = (imply (neg (eqn (param (paramref "i")) (param (paramref "j")))) (imply (eqn (var (arr [("state", [paramref "i"])])) (const _M)) (neg (eqn (var (arr [("state", [paramref "j"])])) (const _M))))) in
  prop name params formula

let properties = [n_coherence]


let protocol = {
  name = "n_mesi";
  types;
  vardefs;
  init;
  rules;
  properties;
}

let () = run_with_cmdline (fun () ->
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol
    ~murphi:(In_channel.read_all "n_mesi.m")
  in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)

