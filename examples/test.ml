
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder

let _True = boolc true
let _False = boolc false

let types = [
  enum "NODE" (int_consts [1; 2; 3; 4]);
  enum "boolean" [_True; _False];
]



let vardefs = List.concat [
  [arrdef "a" [] "boolean"];
  [arrdef "b" [] "boolean"];
  [arrdef "c" [paramdef "i0" "NODE"] "boolean"];
  [arrdef "d" [] "boolean"];
  [arrdef "e" [] "NODE"];
  [arrdef "f" [] "boolean"];
  [arrdef "g" [] "boolean"]
]

let init = (assign (global "a") (const (boolc true)))

let n_NI_InvAck =
  let name = "n_NI_InvAck" in
  let params = [paramdef "src" "NODE"] in
  let formula = (eqn (var (global "a")) (const (boolc true))) in
  let statement = (forStatement (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (eqn (var (arr "c" [paramref "p"])) (const _True))]) (assign (global "e") (param (paramref "p"))) (assign (global "e") (param (paramref "src")))) [paramdef "p" "NODE"]) in
  rule name params formula statement

let rules = [n_NI_InvAck]

let n_MemDataProp =
  let name = "n_MemDataProp" in
  let params = [] in
  let formula = (eqn (var (global "a")) (const _False)) in
  prop name params formula

let properties = [n_MemDataProp]


let protocol = {
  name = "n_test";
  types;
  vardefs;
  init;
  rules;
  properties;
};;

find ~protocol ();;
