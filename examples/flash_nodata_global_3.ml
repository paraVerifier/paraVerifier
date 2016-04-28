
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _CACHE_I = strc "CACHE_I"
let _CACHE_S = strc "CACHE_S"
let _CACHE_E = strc "CACHE_E"
let _NODE_None = strc "NODE_None"
let _NODE_Get = strc "NODE_Get"
let _NODE_GetX = strc "NODE_GetX"
let _UNI_None = strc "UNI_None"
let _UNI_Get = strc "UNI_Get"
let _UNI_GetX = strc "UNI_GetX"
let _UNI_Put = strc "UNI_Put"
let _UNI_PutX = strc "UNI_PutX"
let _UNI_Nak = strc "UNI_Nak"
let _INV_None = strc "INV_None"
let _INV_Inv = strc "INV_Inv"
let _INV_InvAck = strc "INV_InvAck"
let _RP_None = strc "RP_None"
let _RP_Replace = strc "RP_Replace"
let _WB_None = strc "WB_None"
let _WB_Wb = strc "WB_Wb"
let _SHWB_None = strc "SHWB_None"
let _SHWB_ShWb = strc "SHWB_ShWb"
let _SHWB_FAck = strc "SHWB_FAck"
let _NAKC_None = strc "NAKC_None"
let _NAKC_Nakc = strc "NAKC_Nakc"
let _True = boolc true
let _False = boolc false

let types = [
  enum "CACHE_STATE" [_CACHE_I; _CACHE_S; _CACHE_E];
  enum "NODE_CMD" [_NODE_None; _NODE_Get; _NODE_GetX];
  enum "UNI_CMD" [_UNI_None; _UNI_Get; _UNI_GetX; _UNI_Put; _UNI_PutX; _UNI_Nak];
  enum "INV_CMD" [_INV_None; _INV_Inv; _INV_InvAck];
  enum "RP_CMD" [_RP_None; _RP_Replace];
  enum "WB_CMD" [_WB_None; _WB_Wb];
  enum "SHWB_CMD" [_SHWB_None; _SHWB_ShWb; _SHWB_FAck];
  enum "NAKC_CMD" [_NAKC_None; _NAKC_Nakc];
  enum "NODE" (int_consts [1; 2; 3]);
  enum "boolean" [_True; _False];
]

let _NODE_STATE = List.concat [
  [arrdef [("ProcCmd", [])] "NODE_CMD"];
  [arrdef [("InvMarked", [])] "boolean"];
  [arrdef [("CacheState", [])] "CACHE_STATE"]
]

let _DIR_STATE = List.concat [
  [arrdef [("Pending", [])] "boolean"];
  [arrdef [("Local", [])] "boolean"];
  [arrdef [("Dirty", [])] "boolean"];
  [arrdef [("HeadVld", [])] "boolean"];
  [arrdef [("HeadPtr", [])] "NODE"];
  [arrdef [("HomeHeadPtr", [])] "boolean"];
  [arrdef [("ShrVld", [])] "boolean"];
  [arrdef [("ShrSet", [paramdef "i0" "NODE"])] "boolean"];
  [arrdef [("HomeShrSet", [])] "boolean"];
  [arrdef [("InvSet", [paramdef "i1" "NODE"])] "boolean"];
  [arrdef [("HomeInvSet", [])] "boolean"]
]

let _UNI_MSG = List.concat [
  [arrdef [("Cmd", [])] "UNI_CMD"];
  [arrdef [("Proc", [])] "NODE"];
  [arrdef [("HomeProc", [])] "boolean"]
]

let _INV_MSG = List.concat [
  [arrdef [("Cmd", [])] "INV_CMD"]
]

let _RP_MSG = List.concat [
  [arrdef [("Cmd", [])] "RP_CMD"]
]

let _WB_MSG = List.concat [
  [arrdef [("Cmd", [])] "WB_CMD"];
  [arrdef [("Proc", [])] "NODE"];
  [arrdef [("HomeProc", [])] "boolean"]
]

let _SHWB_MSG = List.concat [
  [arrdef [("Cmd", [])] "SHWB_CMD"];
  [arrdef [("Proc", [])] "NODE"];
  [arrdef [("HomeProc", [])] "boolean"]
]

let _NAKC_MSG = List.concat [
  [arrdef [("Cmd", [])] "NAKC_CMD"]
]

let _STATE = List.concat [
  record_def "Proc" [paramdef "i2" "NODE"] _NODE_STATE;
  record_def "HomeProc" [] _NODE_STATE;
  record_def "Dir" [] _DIR_STATE;
  record_def "UniMsg" [paramdef "i3" "NODE"] _UNI_MSG;
  record_def "HomeUniMsg" [] _UNI_MSG;
  record_def "InvMsg" [paramdef "i4" "NODE"] _INV_MSG;
  record_def "HomeInvMsg" [] _INV_MSG;
  record_def "RpMsg" [paramdef "i5" "NODE"] _RP_MSG;
  record_def "HomeRpMsg" [] _RP_MSG;
  record_def "WbMsg" [] _WB_MSG;
  record_def "ShWbMsg" [] _SHWB_MSG;
  record_def "NakcMsg" [] _NAKC_MSG
]

let vardefs = List.concat [
  record_def "Sta" [] _STATE
]

let init = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramfix "h" "NODE" (intc 1)))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (assign (record [global "Sta"; global "WbMsg"; global "Cmd"]) (const _WB_None)); (assign (record [global "Sta"; global "WbMsg"; global "Proc"]) (param (paramfix "h" "NODE" (intc 1)))); (assign (record [global "Sta"; global "WbMsg"; global "HomeProc"]) (const (boolc true))); (assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_None)); (assign (record [global "Sta"; global "ShWbMsg"; global "Proc"]) (param (paramfix "h" "NODE" (intc 1)))); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc true))); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_None)); (forStatement (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "p"])]; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "p"])]; global "Proc"]) (param (paramfix "h" "NODE" (intc 1)))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "p"])]; global "HomeProc"]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("RpMsg", [paramref "p"])]; global "Cmd"]) (const _RP_None))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Proc"]) (param (paramfix "h" "NODE" (intc 1)))); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "HomeRpMsg"; global "Cmd"]) (const _RP_None))])

let n_PI_Remote_Get =
  let name = "n_PI_Remote_Get" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "CacheState"])) (const _CACHE_I))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "ProcCmd"]) (const _NODE_Get)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Get)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc true)))]) in
  rule name params formula statement

let n_PI_Remote_GetX =
  let name = "n_PI_Remote_GetX" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "CacheState"])) (const _CACHE_I))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "ProcCmd"]) (const _NODE_GetX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_GetX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (const (boolc true)))]) in
  rule name params formula statement

let n_PI_Remote_PutX =
  let name = "n_PI_Remote_PutX" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "WbMsg"; global "Cmd"]) (const _WB_Wb)); (assign (record [global "Sta"; global "WbMsg"; global "Proc"]) (param (paramref "dst"))); (assign (record [global "Sta"; global "WbMsg"; global "HomeProc"]) (const (boolc false)))]) in
  rule name params formula statement

let n_PI_Remote_Replace =
  let name = "n_PI_Remote_Replace" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "CacheState"])) (const _CACHE_S))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "src"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"]) (const _RP_Replace))]) in
  rule name params formula statement

let n_NI_Nak =
  let name = "n_NI_Nak" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"])) (const _UNI_Nak)) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Local_Get_Nak =
  let name = "n_NI_Local_Get_Nak" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (orList [(orList [(eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _True)); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _True))]); (neg (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E)))])]); (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const _False))])])]) in
  let statement = (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)) in
  rule name params formula statement

let n_NI_Local_Get_Get =
  let name = "n_NI_Local_Get_Get" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _False))]); (orList [(neg (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const _True))])]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Get)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let n_NI_Local_Get_Put =
  let name = "n_NI_Local_Get_Put" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (neg (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _False))]); (imply (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True)) (andList [(eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _True)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E))]))]) in
  let statement = (ifelseStatement (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True)) (parallel [(assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_S)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Put))]) (parallel [(ifelseStatement (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)) (parallel [(assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "src"])]]) (const (boolc true))); (forStatement (ifelseStatement (orList [(eqn (param (paramref "p")) (param (paramref "src"))); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]) (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))) (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])))]) (parallel [(assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false)))])); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Put))])) in
  rule name params formula statement

let n_NI_Remote_Get_Nak =
  let name = "n_NI_Remote_Get_Nak" in
  let params = [paramdef "src" "NODE"; paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(neg (eqn (param (paramref "src")) (param (paramref "dst")))); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _False))]); (neg (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_Nakc))]) in
  rule name params formula statement

let n_NI_Remote_Get_Nak_Home =
  let name = "n_NI_Remote_Get_Nak_Home" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"])) (const _False))]); (neg (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_Nakc))]) in
  rule name params formula statement

let n_NI_Remote_Get_Put =
  let name = "n_NI_Remote_Get_Put" in
  let params = [paramdef "src" "NODE"; paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(neg (eqn (param (paramref "src")) (param (paramref "dst")))); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_Get))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _False))]); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_S)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Put)); (assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_ShWb)); (assign (record [global "Sta"; global "ShWbMsg"; global "Proc"]) (param (paramref "src"))); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Remote_Get_Put_Home =
  let name = "n_NI_Remote_Get_Put_Home" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_Get)); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"])) (const _False))]); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_S)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_Put))]) in
  rule name params formula statement

let n_NI_Local_GetX_Nak =
  let name = "n_NI_Local_GetX_Nak" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (orList [(orList [(eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _True)); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _True))]); (neg (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E)))])]); (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const _False))])])]) in
  let statement = (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)) in
  rule name params formula statement

let n_NI_Local_GetX_GetX =
  let name = "n_NI_Local_GetX_GetX" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _False))]); (orList [(neg (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src")))); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const _True))])]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_GetX)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let n_NI_Local_GetX_PutX =
  let name = "n_NI_Local_GetX_PutX" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _False))]); (imply (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True)) (andList [(eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _True)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E))]))]) in
  let statement = (ifelseStatement (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True)) (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) (ifelseStatement (imply (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)) (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "src"))); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const _False))]); (forallFormula [paramdef "p" "NODE"] (imply (neg (eqn (param (paramref "p")) (param (paramref "src")))) (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _False))))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])) (const _False))])) (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (ifStatement (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _True)) (parallel [(assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (ifStatement (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get)) (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc true))))]))]) (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (param (paramref "src"))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const _False))])])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (ifStatement (eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _True)) (parallel [(assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (ifStatement (eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_Get)) (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc true))))]))]))) in
  rule name params formula statement

let n_NI_Remote_GetX_Nak =
  let name = "n_NI_Remote_GetX_Nak" in
  let params = [paramdef "src" "NODE"; paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(neg (eqn (param (paramref "src")) (param (paramref "dst")))); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _False))]); (neg (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E)))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_Nakc))]) in
  rule name params formula statement

let n_NI_Remote_GetX_Nak_Home =
  let name = "n_NI_Remote_GetX_Nak_Home" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"])) (const _False))]); (neg (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E)))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_Nak)); (assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_Nakc))]) in
  rule name params formula statement

let n_NI_Remote_GetX_PutX =
  let name = "n_NI_Remote_GetX_PutX" in
  let params = [paramdef "src" "NODE"; paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(andList [(neg (eqn (param (paramref "src")) (param (paramref "dst")))); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"])) (const _UNI_GetX))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "HomeProc"])) (const _False))]); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; arr [("UniMsg", [paramref "src"])]; global "Cmd"]) (const _UNI_PutX)); (assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_FAck)); (assign (record [global "Sta"; global "ShWbMsg"; global "Proc"]) (param (paramref "src"))); (assign (record [global "Sta"; global "ShWbMsg"; global "HomeProc"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Remote_GetX_PutX_Home =
  let name = "n_NI_Remote_GetX_PutX_Home" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_GetX)); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Proc"])) (param (paramref "dst")))]); (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"])) (const _False))]); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_PutX))]) in
  rule name params formula statement

let n_NI_Remote_Put =
  let name = "n_NI_Remote_Put" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"])) (const _UNI_Put)) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"]) (const _NODE_None)); (ifelseStatement (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"])) (const _True)) (parallel [(assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I))]) (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_S)))]) in
  rule name params formula statement

let n_NI_Remote_PutX =
  let name = "n_NI_Remote_PutX" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (andList [(eqn (var (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"])) (const _UNI_PutX)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"])) (const _NODE_GetX))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("UniMsg", [paramref "dst"])]; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_E))]) in
  rule name params formula statement

let n_NI_Inv =
  let name = "n_NI_Inv" in
  let params = [paramdef "dst" "NODE"] in
  let formula = (eqn (var (record [global "Sta"; arr [("InvMsg", [paramref "dst"])]; global "Cmd"])) (const _INV_Inv)) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("InvMsg", [paramref "dst"])]; global "Cmd"]) (const _INV_InvAck)); (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "CacheState"]) (const _CACHE_I)); (ifStatement (eqn (var (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "ProcCmd"])) (const _NODE_Get)) (assign (record [global "Sta"; arr [("Proc", [paramref "dst"])]; global "InvMarked"]) (const (boolc true))))]) in
  rule name params formula statement

let n_NI_InvAck =
  let name = "n_NI_InvAck" in
  let params = [paramdef "src" "NODE"] in
  let formula = (andList [(andList [(eqn (var (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"])) (const _INV_InvAck)); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _True))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("InvMsg", [paramref "src"])]; global "Cmd"]) (const _INV_None)); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]]) (const (boolc false))); (ifStatement (andList [(neg (existFormula [paramdef "p" "NODE"] (andList [(neg (eqn (param (paramref "p")) (param (paramref "src")))); (eqn (var (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]])) (const _True))]))); (eqn (var (record [global "Sta"; global "Dir"; global "HomeInvSet"])) (const _False))]) (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (ifStatement (andList [(eqn (var (record [global "Sta"; global "Dir"; global "Local"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _False))]) (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))))]))]) in
  rule name params formula statement

let n_NI_Replace =
  let name = "n_NI_Replace" in
  let params = [paramdef "src" "NODE"] in
  let formula = (eqn (var (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"])) (const _RP_Replace)) in
  let statement = (parallel [(assign (record [global "Sta"; arr [("RpMsg", [paramref "src"])]; global "Cmd"]) (const _RP_None)); (ifStatement (eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "src"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "src"])]]) (const (boolc false)))]))]) in
  rule name params formula statement

let n_PI_Local_Get_Get =
  let name = "n_PI_Local_Get_Get" in
  let params = [] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_Get)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_Get)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let n_PI_Local_Get_Put =
  let name = "n_PI_Local_Get_Put" in
  let params = [] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I))]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _False))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (ifelseStatement (eqn (var (record [global "Sta"; global "HomeProc"; global "InvMarked"])) (const _True)) (parallel [(assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_S)))]) in
  rule name params formula statement

let n_PI_Local_GetX_GetX =
  let name = "n_PI_Local_GetX_GetX" in
  let params = [] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (orList [(eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_S))])]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_GetX)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_GetX)); (assign (record [global "Sta"; global "HomeUniMsg"; global "Proc"]) (var (record [global "Sta"; global "Dir"; global "HeadPtr"]))); (assign (record [global "Sta"; global "HomeUniMsg"; global "HomeProc"]) (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])))]) in
  rule name params formula statement

let n_PI_Local_GetX_PutX =
  let name = "n_PI_Local_GetX_PutX" in
  let params = [] in
  let formula = (andList [(andList [(andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (orList [(eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_I)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_S))])]); (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _False))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc true))); (ifStatement (eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)) (parallel [(assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc false))); (forStatement (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (ifelseStatement (orList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]); (andList [(andList [(eqn (var (record [global "Sta"; global "Dir"; global "HeadVld"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HeadPtr"])) (param (paramref "p")))]); (eqn (var (record [global "Sta"; global "Dir"; global "HomeHeadPtr"])) (const _False))])]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_Inv))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; arr [("InvMsg", [paramref "p"])]; global "Cmd"]) (const _INV_None))]))]) [paramdef "p" "NODE"]); (assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeInvMsg"; global "Cmd"]) (const _INV_None))])); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_E))]) in
  rule name params formula statement

let n_PI_Local_PutX =
  let name = "n_PI_Local_PutX" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E))]) in
  let statement = (ifelseStatement (eqn (var (record [global "Sta"; global "Dir"; global "Pending"])) (const _True)) (parallel [(assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false)))]) (parallel [(assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I)); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false)))])) in
  rule name params formula statement

let n_PI_Local_Replace =
  let name = "n_PI_Local_Replace" in
  let params = [] in
  let formula = (andList [(eqn (var (record [global "Sta"; global "HomeProc"; global "ProcCmd"])) (const _NODE_None)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_S))]) in
  let statement = (parallel [(assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) in
  rule name params formula statement

let n_NI_Nak_Home =
  let name = "n_NI_Nak_Home" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_Nak)) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Nak_Clear =
  let name = "n_NI_Nak_Clear" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "NakcMsg"; global "Cmd"])) (const _NAKC_Nakc)) in
  let statement = (parallel [(assign (record [global "Sta"; global "NakcMsg"; global "Cmd"]) (const _NAKC_None)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_Local_Put =
  let name = "n_NI_Local_Put" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_Put)) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (ifelseStatement (eqn (var (record [global "Sta"; global "HomeProc"; global "InvMarked"])) (const _True)) (parallel [(assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_I))]) (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_S)))]) in
  rule name params formula statement

let n_NI_Local_PutXAcksDone =
  let name = "n_NI_Local_PutXAcksDone" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "HomeUniMsg"; global "Cmd"])) (const _UNI_PutX)) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeUniMsg"; global "Cmd"]) (const _UNI_None)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Local"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "ProcCmd"]) (const _NODE_None)); (assign (record [global "Sta"; global "HomeProc"; global "InvMarked"]) (const (boolc false))); (assign (record [global "Sta"; global "HomeProc"; global "CacheState"]) (const _CACHE_E))]) in
  rule name params formula statement

let n_NI_Wb =
  let name = "n_NI_Wb" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "WbMsg"; global "Cmd"])) (const _WB_Wb)) in
  let statement = (parallel [(assign (record [global "Sta"; global "WbMsg"; global "Cmd"]) (const _WB_None)); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HeadVld"]) (const (boolc false)))]) in
  rule name params formula statement

let n_NI_FAck =
  let name = "n_NI_FAck" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "ShWbMsg"; global "Cmd"])) (const _SHWB_FAck)) in
  let statement = (parallel [(assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_None)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (ifStatement (eqn (var (record [global "Sta"; global "Dir"; global "Dirty"])) (const _True)) (parallel [(assign (record [global "Sta"; global "Dir"; global "HeadPtr"]) (var (record [global "Sta"; global "ShWbMsg"; global "Proc"]))); (assign (record [global "Sta"; global "Dir"; global "HomeHeadPtr"]) (var (record [global "Sta"; global "ShWbMsg"; global "HomeProc"])))]))]) in
  rule name params formula statement

let n_NI_ShWb =
  let name = "n_NI_ShWb" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "ShWbMsg"; global "Cmd"])) (const _SHWB_ShWb)) in
  let statement = (parallel [(assign (record [global "Sta"; global "ShWbMsg"; global "Cmd"]) (const _SHWB_None)); (assign (record [global "Sta"; global "Dir"; global "Pending"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "Dirty"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "ShrVld"]) (const (boolc true))); (forStatement (ifelseStatement (orList [(andList [(eqn (param (paramref "p")) (var (record [global "Sta"; global "ShWbMsg"; global "Proc"]))); (eqn (var (record [global "Sta"; global "ShWbMsg"; global "HomeProc"])) (const _False))]); (eqn (var (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]])) (const _True))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc true)))]) (parallel [(assign (record [global "Sta"; global "Dir"; arr [("ShrSet", [paramref "p"])]]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; arr [("InvSet", [paramref "p"])]]) (const (boolc false)))])) [paramdef "p" "NODE"]); (ifelseStatement (orList [(eqn (var (record [global "Sta"; global "ShWbMsg"; global "HomeProc"])) (const _True)); (eqn (var (record [global "Sta"; global "Dir"; global "HomeShrSet"])) (const _True))]) (parallel [(assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc true))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc true)))]) (parallel [(assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false)))]))]) in
  rule name params formula statement

let n_NI_Replace_Home =
  let name = "n_NI_Replace_Home" in
  let params = [] in
  let formula = (eqn (var (record [global "Sta"; global "HomeRpMsg"; global "Cmd"])) (const _RP_Replace)) in
  let statement = (parallel [(assign (record [global "Sta"; global "HomeRpMsg"; global "Cmd"]) (const _RP_None)); (ifStatement (eqn (var (record [global "Sta"; global "Dir"; global "ShrVld"])) (const _True)) (parallel [(assign (record [global "Sta"; global "Dir"; global "HomeShrSet"]) (const (boolc false))); (assign (record [global "Sta"; global "Dir"; global "HomeInvSet"]) (const (boolc false)))]))]) in
  rule name params formula statement

let rules = [n_PI_Remote_Get; n_PI_Remote_GetX; n_PI_Remote_PutX; n_PI_Remote_Replace; n_NI_Nak; n_NI_Local_Get_Nak; n_NI_Local_Get_Get; n_NI_Local_Get_Put; n_NI_Remote_Get_Nak; n_NI_Remote_Get_Nak_Home; n_NI_Remote_Get_Put; n_NI_Remote_Get_Put_Home; n_NI_Local_GetX_Nak; n_NI_Local_GetX_GetX; n_NI_Local_GetX_PutX; n_NI_Remote_GetX_Nak; n_NI_Remote_GetX_Nak_Home; n_NI_Remote_GetX_PutX; n_NI_Remote_GetX_PutX_Home; n_NI_Remote_Put; n_NI_Remote_PutX; n_NI_Inv; n_NI_InvAck; n_NI_Replace; n_PI_Local_Get_Get; n_PI_Local_Get_Put; n_PI_Local_GetX_GetX; n_PI_Local_GetX_PutX; n_PI_Local_PutX; n_PI_Local_Replace; n_NI_Nak_Home; n_NI_Nak_Clear; n_NI_Local_Put; n_NI_Local_PutXAcksDone; n_NI_Wb; n_NI_FAck; n_NI_ShWb; n_NI_Replace_Home]

let n_CacheStateProp =
  let name = "n_CacheStateProp" in
  let params = [] in
  let formula = (forallFormula [paramdef "p" "NODE"] (forallFormula [paramdef "q" "NODE"] (imply (neg (eqn (param (paramref "p")) (param (paramref "q")))) (neg (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "CacheState"])) (const _CACHE_E)); (eqn (var (record [global "Sta"; arr [("Proc", [paramref "q"])]; global "CacheState"])) (const _CACHE_E))]))))) in
  prop name params formula

let n_CacheStatePropHome =
  let name = "n_CacheStatePropHome" in
  let params = [] in
  let formula = (forallFormula [paramdef "p" "NODE"] (neg (andList [(eqn (var (record [global "Sta"; arr [("Proc", [paramref "p"])]; global "CacheState"])) (const _CACHE_E)); (eqn (var (record [global "Sta"; global "HomeProc"; global "CacheState"])) (const _CACHE_E))]))) in
  prop name params formula

let properties = [n_CacheStateProp; n_CacheStatePropHome]


let protocol = {
  name = "n_flash_nodata_global";
  types;
  vardefs;
  init;
  rules;
  properties;
}

let () = run_with_cmdline (fun () ->
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol
    ~murphi:(In_channel.read_all "n_flash_nodata_global.m")
    ~smv:(In_channel.read_all "flash_nodata.smv")
    ~smv_escape:(fun inv_str ->
      let replace s d =
        Re2.Regex.rewrite_exn (Re2.Regex.of_string s) ~template:d
      in
      inv_str
      |> replace "HomeHeadPtr = FALSE" "HeadPtr != 0"
      |> replace "HomeHeadPtr = TRUE" "HeadPtr = 0"
      |> replace "HomeShrSet" "ShrSet[0]"
      |> replace "HomeInvSet" "InvSet[0]"
      |> replace "HomeProc = FALSE" "Proc != 0"
      |> replace "HomeProc = TRUE" "Proc = 0"
      |> replace "HomeProc\\." "Proc[0]."
      |> replace "HomeUniMsg" "UniMsg[0]"
      |> replace "HomeInvMsg" "InvMsg[0]"
      |> replace "HomeRpMsg" "RpMsg[0]"
    )
  in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)

