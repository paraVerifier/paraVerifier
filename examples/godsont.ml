
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _INVALID = strc "INVALID"
let _DIRTY = strc "DIRTY"
let _VALID = strc "VALID"
let _NON = strc "NON"
let _REQUIRE = strc "REQUIRE"
let _REQREPALL = strc "REQREPALL"
let _RANDOM = strc "RANDOM"
let _RANDINV = strc "RANDINV"
let _DESIGNATED = strc "DESIGNATED"
let _TOREP = strc "TOREP"
let _DONE = strc "DONE"
let _REPALLDONE = strc "REPALLDONE"
let _NONE = strc "NONE"
let _NLNCR = strc "NLNCR"
let _NLNCW = strc "NLNCW"
let _LNCFR = strc "LNCFR"
let _LCFR = strc "LCFR"
let _LNCNFR = strc "LNCNFR"
let _True = boolc true
let _False = boolc false

let types = [
  enum "CACHE_STATE" [_INVALID; _DIRTY; _VALID];
  enum "REPLACE_STAGE" [_NON; _REQUIRE; _REQREPALL; _RANDOM; _RANDINV; _DESIGNATED; _TOREP; _DONE; _REPALLDONE];
  enum "REPLACE_RULE" [_NONE; _NLNCR; _NLNCW; _LNCFR; _LCFR; _LNCNFR];
  enum "TYPE_NODE" (int_consts [1; 2]);
  enum "TYPE_CACHE" (int_consts [1; 2]);
  enum "TYPE_ADDR" (int_consts [1; 2]);
  enum "TYPE_DATA" (int_consts [1; 2]);
  enum "TYPE_LOCK" (int_consts [1; 2]);
  enum "boolean" [_True; _False];
]

let _CACHE = List.concat [
  [arrdef [("state", [])] "CACHE_STATE"];
  [arrdef [("addr", [])] "TYPE_ADDR"];
  [arrdef [("data", [])] "TYPE_DATA"]
]

let _MEMORY = List.concat [
  [arrdef [("data", [])] "TYPE_DATA"]
]

let _LOCK = List.concat [
  [arrdef [("owner", [])] "TYPE_NODE"];
  [arrdef [("beUsed", [])] "boolean"];
  [arrdef [("inProtection", [paramdef "i0" "TYPE_ADDR"])] "boolean"]
]

let _NODE = List.concat [
  record_def "cache" [paramdef "i1" "TYPE_CACHE"] _CACHE;
  [arrdef [("hasLock", [])] "boolean"];
  [arrdef [("firstRead", [paramdef "i2" "TYPE_ADDR"])] "boolean"]
]

let vardefs = List.concat [
  record_def "memory" [paramdef "i3" "TYPE_ADDR"] _MEMORY;
  record_def "lock" [paramdef "i4" "TYPE_LOCK"] _LOCK;
  record_def "node" [paramdef "i5" "TYPE_NODE"] _NODE;
  [arrdef [("curNode", [])] "TYPE_NODE"];
  [arrdef [("curCache", [])] "TYPE_CACHE"];
  [arrdef [("curMemory", [])] "TYPE_ADDR"];
  [arrdef [("curData", [])] "TYPE_DATA"];
  [arrdef [("curLock", [])] "TYPE_LOCK"];
  [arrdef [("replace", [])] "REPLACE_STAGE"];
  [arrdef [("repRule", [])] "REPLACE_RULE"]
]

let init = (parallel [(forStatement (parallel [(forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _INVALID)) [paramdef "j" "TYPE_CACHE"]); (assign (record [arr [("node", [paramref "i"])]; global "hasLock"]) (const (boolc false))); (forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("firstRead", [paramref "a"])]]) (const (boolc true))) [paramdef "a" "TYPE_ADDR"]); (assign (global "curNode") (param (paramref "i")))]) [paramdef "i" "TYPE_NODE"]); (forStatement (assign (global "curCache") (param (paramref "j"))) [paramdef "j" "TYPE_CACHE"]); (forStatement (parallel [(assign (record [arr [("memory", [paramref "a"])]; global "data"]) (param (paramfix "d" "TYPE_DATA" (intc 1)))); (assign (global "curMemory") (param (paramref "a")))]) [paramdef "a" "TYPE_ADDR"]); (assign (global "curData") (param (paramfix "d" "TYPE_DATA" (intc 1)))); (forStatement (parallel [(assign (record [arr [("lock", [paramref "l"])]; global "beUsed"]) (const (boolc false))); (assign (global "curLock") (param (paramref "l"))); (forStatement (assign (record [arr [("lock", [paramref "l"])]; arr [("inProtection", [paramref "a"])]]) (const (boolc false))) [paramdef "a" "TYPE_ADDR"])]) [paramdef "l" "TYPE_LOCK"]); (assign (global "replace") (const _NON)); (assign (global "repRule") (const _NONE))])

let n_RI =
  let name = "n_RI" in
  let params = [paramdef "i" "TYPE_NODE"] in
  let formula = (andList [(andList [(eqn (var (global "replace")) (const _REQUIRE)); (eqn (param (paramref "i")) (var (global "curNode")))]); (existFormula [paramdef "j" "TYPE_CACHE"] (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID)))]) in
  let statement = (assign (global "replace") (const _RANDINV)) in
  rule name params formula statement

let n_CRIC =
  let name = "n_CRIC" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"] in
  let formula = (andList [(andList [(eqn (var (global "replace")) (const _RANDINV)); (eqn (param (paramref "i")) (var (global "curNode")))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID))]) in
  let statement = (parallel [(assign (global "curCache") (param (paramref "j"))); (assign (global "replace") (const _DONE))]) in
  rule name params formula statement

let n_RNI =
  let name = "n_RNI" in
  let params = [paramdef "i" "TYPE_NODE"] in
  let formula = (andList [(andList [(eqn (var (global "replace")) (const _REQUIRE)); (eqn (param (paramref "i")) (var (global "curNode")))]); (forallFormula [paramdef "j" "TYPE_CACHE"] (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID))))]) in
  let statement = (assign (global "replace") (const _RANDOM)) in
  rule name params formula statement

let n_CRC =
  let name = "n_CRC" in
  let params = [paramdef "i" "TYPE_CACHE"] in
  let formula = (eqn (var (global "replace")) (const _RANDOM)) in
  let statement = (parallel [(assign (global "curCache") (param (paramref "i"))); (assign (global "replace") (const _DESIGNATED))]) in
  rule name params formula statement

let n_DCND =
  let name = "n_DCND" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"] in
  let formula = (andList [(andList [(andList [(eqn (var (global "replace")) (const _DESIGNATED)); (eqn (param (paramref "i")) (var (global "curNode")))]); (eqn (param (paramref "j")) (var (global "curCache")))]); (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _DIRTY)))]) in
  let statement = (assign (global "replace") (const _DONE)) in
  rule name params formula statement

let n_DCD =
  let name = "n_DCD" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"] in
  let formula = (andList [(andList [(andList [(eqn (var (global "replace")) (const _DESIGNATED)); (eqn (param (paramref "i")) (var (global "curNode")))]); (eqn (param (paramref "j")) (var (global "curCache")))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _DIRTY))]) in
  let statement = (assign (global "replace") (const _TOREP)) in
  rule name params formula statement

let n_Replace =
  let name = "n_Replace" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"] in
  let formula = (andList [(andList [(andList [(eqn (var (global "replace")) (const _TOREP)); (eqn (param (paramref "i")) (var (global "curNode")))]); (eqn (param (paramref "j")) (var (global "curCache")))]); (eqn (param (paramref "a")) (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])))]) in
  let statement = (parallel [(assign (record [arr [("memory", [paramref "a"])]; global "data"]) (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"]))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _INVALID)); (assign (global "replace") (const _DONE))]) in
  rule name params formula statement

let n_RepAll =
  let name = "n_RepAll" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"] in
  let formula = (andList [(andList [(eqn (var (global "replace")) (const _REQREPALL)); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _DIRTY))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])) (param (paramref "a")))]) in
  let statement = (parallel [(assign (record [arr [("memory", [paramref "a"])]; global "data"]) (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"]))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _INVALID))]) in
  rule name params formula statement

let n_NLNCRR =
  let name = "n_NLNCRR" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "a" "TYPE_ADDR"] in
  let formula = (andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _False))]); (forallFormula [paramdef "j" "TYPE_CACHE"] (orList [(eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID)); (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])) (param (paramref "a"))))]))]) in
  let statement = (parallel [(assign (global "curNode") (param (paramref "i"))); (assign (global "curMemory") (param (paramref "a"))); (assign (global "replace") (const _REQUIRE)); (assign (global "repRule") (const _NLNCR))]) in
  rule name params formula statement

let n_NLNCRD =
  let name = "n_NLNCRD" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _DONE)); (eqn (var (global "repRule")) (const _NLNCR))]); (eqn (param (paramref "i")) (var (global "curNode")))]); (eqn (param (paramref "j")) (var (global "curCache")))]); (eqn (param (paramref "a")) (var (global "curMemory")))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"]) (param (paramref "a"))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"]) (var (record [arr [("memory", [paramref "a"])]; global "data"]))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _VALID)); (assign (global "replace") (const _NON)); (assign (global "repRule") (const _NONE))]) in
  rule name params formula statement

let n_NLCW =
  let name = "n_NLCW" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"; paramdef "d" "TYPE_DATA"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _False))]); (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID)))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])) (param (paramref "a")))]); (forallFormula [paramdef "l" "TYPE_LOCK"] (eqn (var (record [arr [("lock", [paramref "l"])]; arr [("inProtection", [paramref "a"])]])) (const _False)))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"]) (param (paramref "d"))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _DIRTY))]) in
  rule name params formula statement

let n_NLNCWR =
  let name = "n_NLNCWR" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "a" "TYPE_ADDR"; paramdef "d" "TYPE_DATA"] in
  let formula = (andList [(andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _False))]); (forallFormula [paramdef "j" "TYPE_CACHE"] (orList [(eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID)); (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])) (param (paramref "a"))))]))]); (forallFormula [paramdef "l" "TYPE_LOCK"] (eqn (var (record [arr [("lock", [paramref "l"])]; arr [("inProtection", [paramref "a"])]])) (const _False)))]) in
  let statement = (parallel [(assign (global "curNode") (param (paramref "i"))); (assign (global "curMemory") (param (paramref "a"))); (assign (global "curData") (param (paramref "d"))); (assign (global "replace") (const _REQUIRE)); (assign (global "repRule") (const _NLNCW))]) in
  rule name params formula statement

let n_NLNCWD =
  let name = "n_NLNCWD" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"; paramdef "d" "TYPE_DATA"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _DONE)); (eqn (var (global "repRule")) (const _NLNCW))]); (eqn (param (paramref "i")) (var (global "curNode")))]); (eqn (param (paramref "j")) (var (global "curCache")))]); (eqn (param (paramref "a")) (var (global "curMemory")))]); (eqn (param (paramref "d")) (var (global "curData")))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"]) (param (paramref "a"))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"]) (param (paramref "d"))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _DIRTY)); (assign (global "replace") (const _NON)); (assign (global "repRule") (const _NONE))]) in
  rule name params formula statement

let n_LCFRRA =
  let name = "n_LCFRRA" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"; paramdef "l" "TYPE_LOCK"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "beUsed"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "owner"])) (param (paramref "i")))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("firstRead", [paramref "a"])]])) (const _True))]); (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID)))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])) (param (paramref "a")))]) in
  let statement = (parallel [(assign (global "curNode") (param (paramref "i"))); (assign (global "curCache") (param (paramref "j"))); (assign (global "curMemory") (param (paramref "a"))); (assign (global "curLock") (param (paramref "l"))); (assign (global "replace") (const _REQREPALL)); (assign (global "repRule") (const _LCFR))]) in
  rule name params formula statement

let n_LCFRD =
  let name = "n_LCFRD" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"; paramdef "l" "TYPE_LOCK"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _DONE)); (eqn (var (global "repRule")) (const _LCFR))]); (eqn (param (paramref "i")) (var (global "curNode")))]); (eqn (param (paramref "j")) (var (global "curCache")))]); (eqn (param (paramref "a")) (var (global "curMemory")))]); (eqn (param (paramref "l")) (var (global "curLock")))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"]) (var (record [arr [("memory", [paramref "a"])]; global "data"]))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _VALID)); (assign (record [arr [("node", [paramref "i"])]; arr [("firstRead", [paramref "a"])]]) (const (boolc false))); (assign (record [arr [("lock", [paramref "l"])]; arr [("inProtection", [paramref "a"])]]) (const (boolc true))); (assign (global "replace") (const _NON)); (assign (global "repRule") (const _NONE))]) in
  rule name params formula statement

let n_LNCFRRA =
  let name = "n_LNCFRRA" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "a" "TYPE_ADDR"; paramdef "l" "TYPE_LOCK"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "beUsed"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "owner"])) (param (paramref "i")))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("firstRead", [paramref "a"])]])) (const _True))]); (forallFormula [paramdef "j" "TYPE_CACHE"] (orList [(eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID)); (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])) (param (paramref "a"))))]))]) in
  let statement = (parallel [(assign (global "curNode") (param (paramref "i"))); (assign (global "curMemory") (param (paramref "a"))); (assign (global "curLock") (param (paramref "l"))); (assign (global "replace") (const _REQREPALL)); (assign (global "repRule") (const _LNCFR))]) in
  rule name params formula statement

let n_LNCFRD =
  let name = "n_LNCFRD" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"; paramdef "l" "TYPE_LOCK"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _DONE)); (eqn (var (global "repRule")) (const _LNCFR))]); (eqn (param (paramref "i")) (var (global "curNode")))]); (eqn (param (paramref "j")) (var (global "curCache")))]); (eqn (param (paramref "a")) (var (global "curMemory")))]); (eqn (param (paramref "l")) (var (global "curLock")))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"]) (param (paramref "a"))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"]) (var (record [arr [("memory", [paramref "a"])]; global "data"]))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _VALID)); (assign (record [arr [("node", [paramref "i"])]; arr [("firstRead", [paramref "a"])]]) (const (boolc false))); (assign (record [arr [("lock", [paramref "l"])]; arr [("inProtection", [paramref "a"])]]) (const (boolc true))); (assign (global "replace") (const _NON)); (assign (global "repRule") (const _NONE))]) in
  rule name params formula statement

let n_LNCNFRR =
  let name = "n_LNCNFRR" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "a" "TYPE_ADDR"; paramdef "l" "TYPE_LOCK"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "beUsed"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "owner"])) (param (paramref "i")))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("firstRead", [paramref "a"])]])) (const _False))]); (forallFormula [paramdef "j" "TYPE_CACHE"] (orList [(eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID)); (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])) (param (paramref "a"))))]))]) in
  let statement = (parallel [(assign (global "curNode") (param (paramref "i"))); (assign (global "curMemory") (param (paramref "a"))); (assign (global "curLock") (param (paramref "l"))); (assign (global "replace") (const _REQUIRE)); (assign (global "repRule") (const _LNCNFR))]) in
  rule name params formula statement

let n_LNCNFRD =
  let name = "n_LNCNFRD" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"; paramdef "l" "TYPE_LOCK"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _DONE)); (eqn (var (global "repRule")) (const _LNCNFR))]); (eqn (param (paramref "i")) (var (global "curNode")))]); (eqn (param (paramref "j")) (var (global "curCache")))]); (eqn (param (paramref "a")) (var (global "curMemory")))]); (eqn (param (paramref "l")) (var (global "curLock")))]) in
  let statement = (parallel [(assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"]) (param (paramref "a"))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"]) (var (record [arr [("memory", [paramref "a"])]; global "data"]))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _VALID)); (assign (record [arr [("lock", [paramref "l"])]; arr [("inProtection", [paramref "a"])]]) (const (boolc true))); (assign (global "replace") (const _NON)); (assign (global "repRule") (const _NONE))]) in
  rule name params formula statement

let n_LCW =
  let name = "n_LCW" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"; paramdef "d" "TYPE_DATA"; paramdef "l" "TYPE_LOCK"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "beUsed"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "owner"])) (param (paramref "i")))]); (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID)))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])) (param (paramref "a")))]); (forallFormula [paramdef "m" "TYPE_LOCK"] (imply (eqn (var (record [arr [("lock", [paramref "m"])]; arr [("inProtection", [paramref "a"])]])) (const _True)) (eqn (param (paramref "m")) (param (paramref "l")))))]) in
  let statement = (parallel [(assign (record [arr [("memory", [paramref "a"])]; global "data"]) (param (paramref "d"))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"]) (param (paramref "d"))); (assign (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"]) (const _VALID)); (assign (record [arr [("lock", [paramref "l"])]; arr [("inProtection", [paramref "a"])]]) (const (boolc true)))]) in
  rule name params formula statement

let n_LNCW =
  let name = "n_LNCW" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "a" "TYPE_ADDR"; paramdef "d" "TYPE_DATA"; paramdef "l" "TYPE_LOCK"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "beUsed"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "owner"])) (param (paramref "i")))]); (forallFormula [paramdef "j" "TYPE_CACHE"] (orList [(eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _INVALID)); (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])) (param (paramref "a"))))]))]); (forallFormula [paramdef "m" "TYPE_LOCK"] (imply (eqn (var (record [arr [("lock", [paramref "m"])]; arr [("inProtection", [paramref "a"])]])) (const _True)) (eqn (param (paramref "m")) (param (paramref "l")))))]) in
  let statement = (parallel [(assign (record [arr [("memory", [paramref "a"])]; global "data"]) (param (paramref "d"))); (assign (record [arr [("lock", [paramref "l"])]; arr [("inProtection", [paramref "a"])]]) (const (boolc true)))]) in
  rule name params formula statement

let n_Acquire =
  let name = "n_Acquire" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "l" "TYPE_LOCK"] in
  let formula = (andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _False))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "beUsed"])) (const _False))]) in
  let statement = (parallel [(assign (record [arr [("lock", [paramref "l"])]; global "beUsed"]) (const (boolc true))); (assign (record [arr [("lock", [paramref "l"])]; global "owner"]) (param (paramref "i"))); (assign (record [arr [("node", [paramref "i"])]; global "hasLock"]) (const (boolc true))); (forStatement (assign (record [arr [("node", [paramref "i"])]; arr [("firstRead", [paramref "j"])]]) (const (boolc true))) [paramdef "j" "TYPE_ADDR"])]) in
  rule name params formula statement

let n_Release =
  let name = "n_Release" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "l" "TYPE_LOCK"] in
  let formula = (andList [(andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "beUsed"])) (const _True))]); (eqn (var (record [arr [("lock", [paramref "l"])]; global "owner"])) (param (paramref "i")))]) in
  let statement = (parallel [(assign (record [arr [("lock", [paramref "l"])]; global "beUsed"]) (const (boolc false))); (assign (record [arr [("node", [paramref "i"])]; global "hasLock"]) (const (boolc false))); (forStatement (assign (record [arr [("lock", [paramref "l"])]; arr [("inProtection", [paramref "a"])]]) (const (boolc false))) [paramdef "a" "TYPE_ADDR"])]) in
  rule name params formula statement

let n_RepAllDone =
  let name = "n_RepAllDone" in
  let params = [] in
  let formula = (andList [(eqn (var (global "replace")) (const _REQREPALL)); (forallFormula [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"] (neg (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _DIRTY))))]) in
  let statement = (assign (global "replace") (const _REPALLDONE)) in
  rule name params formula statement

let n_LCFRAD =
  let name = "n_LCFRAD" in
  let params = [] in
  let formula = (andList [(eqn (var (global "replace")) (const _REPALLDONE)); (eqn (var (global "repRule")) (const _LCFR))]) in
  let statement = (assign (global "replace") (const _DESIGNATED)) in
  rule name params formula statement

let n_LNCFRAD =
  let name = "n_LNCFRAD" in
  let params = [] in
  let formula = (andList [(eqn (var (global "replace")) (const _REPALLDONE)); (eqn (var (global "repRule")) (const _LNCFR))]) in
  let statement = (assign (global "replace") (const _REQUIRE)) in
  rule name params formula statement

let rules = [n_RI; n_CRIC; n_RNI; n_CRC; n_DCND; n_DCD; n_Replace; n_RepAll; n_NLNCRR; n_NLNCRD; n_NLCW; n_NLNCWR; n_NLNCWD; n_LCFRRA; n_LCFRD; n_LNCFRRA; n_LNCFRD; n_LNCNFRR; n_LNCNFRD; n_LCW; n_LNCW; n_Acquire; n_Release; n_RepAllDone; n_LCFRAD; n_LNCFRAD]

let n_DeadlockFree =
  let name = "n_DeadlockFree" in
  let params = [paramdef "i" "TYPE_NODE"] in
  let formula = (imply (andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _True))]) (andList [(existFormula [paramdef "l" "TYPE_LOCK"] (andList [(eqn (var (record [arr [("lock", [paramref "l"])]; global "beUsed"])) (const _True)); (eqn (var (record [arr [("lock", [paramref "l"])]; global "owner"])) (param (paramref "i")))])); (forallFormula [paramdef "m" "TYPE_LOCK"; paramdef "n" "TYPE_LOCK"] (orList [(orList [(orList [(orList [(eqn (param (paramref "m")) (param (paramref "n"))); (eqn (var (record [arr [("lock", [paramref "m"])]; global "beUsed"])) (const _False))]); (eqn (var (record [arr [("lock", [paramref "n"])]; global "beUsed"])) (const _False))]); (neg (eqn (var (record [arr [("lock", [paramref "m"])]; global "owner"])) (param (paramref "i"))))]); (neg (eqn (var (record [arr [("lock", [paramref "n"])]; global "owner"])) (param (paramref "i"))))]))])) in
  prop name params formula

let n_Coherence =
  let name = "n_Coherence" in
  let params = [paramdef "i" "TYPE_NODE"; paramdef "j" "TYPE_CACHE"; paramdef "a" "TYPE_ADDR"] in
  let formula = (imply (andList [(andList [(andList [(andList [(eqn (var (global "replace")) (const _NON)); (eqn (var (record [arr [("node", [paramref "i"])]; global "hasLock"])) (const _True))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("firstRead", [paramref "a"])]])) (const _False))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "state"])) (const _VALID))]); (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "addr"])) (param (paramref "a")))]) (eqn (var (record [arr [("node", [paramref "i"])]; arr [("cache", [paramref "j"])]; global "data"])) (var (record [arr [("memory", [paramref "a"])]; global "data"])))) in
  prop name params formula

let properties = [n_DeadlockFree; n_Coherence]


let protocol = {
  name = "n_godsont";
  types;
  vardefs;
  init;
  rules;
  properties;
}

let () = run_with_cmdline (fun () ->
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol
    ~murphi:(In_channel.read_all "n_godsont.m")
  in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)

