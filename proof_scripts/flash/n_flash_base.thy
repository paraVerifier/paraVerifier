(*  Title:      HOL/Auth/n_flash_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_flash Protocol Case Study*} 

theory n_flash_base imports paraTheory
begin

section{*Main definitions*}

subsection{* Definitions of Constants*}
definition CACHE_I::"scalrValueType" where [simp]: "CACHE_I\<equiv> enum ''control'' ''CACHE_I''"
definition CACHE_S::"scalrValueType" where [simp]: "CACHE_S\<equiv> enum ''control'' ''CACHE_S''"
definition CACHE_E::"scalrValueType" where [simp]: "CACHE_E\<equiv> enum ''control'' ''CACHE_E''"
definition NODE_None::"scalrValueType" where [simp]: "NODE_None\<equiv> enum ''control'' ''NODE_None''"
definition NODE_Get::"scalrValueType" where [simp]: "NODE_Get\<equiv> enum ''control'' ''NODE_Get''"
definition NODE_GetX::"scalrValueType" where [simp]: "NODE_GetX\<equiv> enum ''control'' ''NODE_GetX''"
definition UNI_None::"scalrValueType" where [simp]: "UNI_None\<equiv> enum ''control'' ''UNI_None''"
definition UNI_Get::"scalrValueType" where [simp]: "UNI_Get\<equiv> enum ''control'' ''UNI_Get''"
definition UNI_GetX::"scalrValueType" where [simp]: "UNI_GetX\<equiv> enum ''control'' ''UNI_GetX''"
definition UNI_Put::"scalrValueType" where [simp]: "UNI_Put\<equiv> enum ''control'' ''UNI_Put''"
definition UNI_PutX::"scalrValueType" where [simp]: "UNI_PutX\<equiv> enum ''control'' ''UNI_PutX''"
definition UNI_Nak::"scalrValueType" where [simp]: "UNI_Nak\<equiv> enum ''control'' ''UNI_Nak''"
definition INV_None::"scalrValueType" where [simp]: "INV_None\<equiv> enum ''control'' ''INV_None''"
definition INV_Inv::"scalrValueType" where [simp]: "INV_Inv\<equiv> enum ''control'' ''INV_Inv''"
definition INV_InvAck::"scalrValueType" where [simp]: "INV_InvAck\<equiv> enum ''control'' ''INV_InvAck''"
definition RP_None::"scalrValueType" where [simp]: "RP_None\<equiv> enum ''control'' ''RP_None''"
definition RP_Replace::"scalrValueType" where [simp]: "RP_Replace\<equiv> enum ''control'' ''RP_Replace''"
definition WB_None::"scalrValueType" where [simp]: "WB_None\<equiv> enum ''control'' ''WB_None''"
definition WB_Wb::"scalrValueType" where [simp]: "WB_Wb\<equiv> enum ''control'' ''WB_Wb''"
definition SHWB_None::"scalrValueType" where [simp]: "SHWB_None\<equiv> enum ''control'' ''SHWB_None''"
definition SHWB_ShWb::"scalrValueType" where [simp]: "SHWB_ShWb\<equiv> enum ''control'' ''SHWB_ShWb''"
definition SHWB_FAck::"scalrValueType" where [simp]: "SHWB_FAck\<equiv> enum ''control'' ''SHWB_FAck''"
definition NAKC_None::"scalrValueType" where [simp]: "NAKC_None\<equiv> enum ''control'' ''NAKC_None''"
definition NAKC_Nakc::"scalrValueType" where [simp]: "NAKC_Nakc\<equiv> enum ''control'' ''NAKC_Nakc''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"



subsection{*  Definitions of Parameterized Rules *}

definition n_Store::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_Store  src data\<equiv>
let g = (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''CacheState'')) (Const CACHE_E)) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''CacheData''), (Const (index data)))), (assign ((Field (Ident ''Sta'') ''CurrData''), (Const (index data))))]) in
guard g s"

definition n_Store_Home::"nat \<Rightarrow> rule" where [simp]:
"n_Store_Home  data\<equiv>
let g = (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E)) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData''), (Const (index data)))), (assign ((Field (Ident ''Sta'') ''CurrData''), (Const (index data))))]) in
guard g s"

definition n_PI_Remote_Get::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_Get  src\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''CacheState'')) (Const CACHE_I)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''ProcCmd'')) (Const NODE_None))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''ProcCmd''), (Const NODE_Get))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Get))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc''), (Const true)))]) in
guard g s"

definition n_PI_Remote_GetX::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_GetX  src\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''CacheState'')) (Const CACHE_I)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''ProcCmd'')) (Const NODE_None))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''ProcCmd''), (Const NODE_GetX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_GetX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc''), (Const true)))]) in
guard g s"

definition n_PI_Remote_PutX::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_PutX  dst\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''ProcCmd'')) (Const NODE_None))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState''), (Const CACHE_I))), (assign ((Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd''), (Const WB_Wb))), (assign ((Field (Field (Ident ''Sta'') ''WbMsg'') ''Proc''), (Const (index dst)))), (assign ((Field (Field (Ident ''Sta'') ''WbMsg'') ''HomeProc''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''WbMsg'') ''Data''), (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheData''))))]) in
guard g s"

definition n_PI_Remote_Replace::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Remote_Replace  src\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''CacheState'')) (Const CACHE_S)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''ProcCmd'')) (Const NODE_None))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') src) ''CacheState''), (Const CACHE_I))), (assign ((Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd''), (Const RP_Replace)))]) in
guard g s"

definition n_NI_Nak::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Nak  dst\<equiv>
let g = (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') dst) ''Cmd'')) (Const UNI_Nak)) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') dst) ''Cmd''), (Const UNI_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''ProcCmd''), (Const NODE_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''InvMarked''), (Const false)))]) in
guard g s"

definition n_NI_Local_Get_Nak__part__0::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Nak__part__0  src\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd'')) (Const RP_Replace)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Nak)))]) in
guard g s"

definition n_NI_Local_Get_Nak__part__1::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Nak__part__1  src\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd'')) (Const RP_Replace)))) (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false)))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Nak)))]) in
guard g s"

definition n_NI_Local_Get_Nak__part__2::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Nak__part__2  src\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd'')) (Const RP_Replace)))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Nak)))]) in
guard g s"

definition n_NI_Local_Get_Get__part__0::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Get__part__0  src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd'')) (Const RP_Replace)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Get))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Proc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''))))]) in
guard g s"

definition n_NI_Local_Get_Get__part__1::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Get__part__1  src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd'')) (Const RP_Replace)))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src))))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Get))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Proc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''))))]) in
guard g s"

definition n_NI_Local_Get_Put_Head::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Put_Head N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd'')) (Const RP_Replace)))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const true))), (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') src), (Const true))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (eqn (Const (index p)) (Const (index src))) (Const true) (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p))))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Put))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData''))))]) in
guard g s"

definition n_NI_Local_Get_Put::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Put  src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd'')) (Const RP_Replace)))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Put))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData''))))]) in
guard g s"

definition n_NI_Local_Get_Put_Dirty::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_Get_Put_Dirty  src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd'')) (Const RP_Replace)))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Ident ''Sta'') ''MemData''), (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_S))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Put))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData''))))]) in
guard g s"

definition n_NI_Remote_Get_Nak::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak  src dst\<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Proc'')) (Const (index dst)))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState'')) (Const CACHE_E)))) (neg (eqn (Const (index src)) (Const (index dst))))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Nak))), (assign ((Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd''), (Const NAKC_Nakc)))]) in
guard g s"

definition n_NI_Remote_Get_Nak_Home::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Nak_Home  dst\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Proc'')) (Const (index dst)))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState'')) (Const CACHE_E)))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd''), (Const UNI_Nak))), (assign ((Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd''), (Const NAKC_Nakc)))]) in
guard g s"

definition n_NI_Remote_Get_Put::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put  src dst\<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Proc'')) (Const (index dst)))) (neg (eqn (Const (index src)) (Const (index dst))))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState''), (Const CACHE_S))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Put))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheData'')))), (assign ((Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd''), (Const SHWB_ShWb))), (assign ((Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Proc''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''ShWbMsg'') ''HomeProc''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Data''), (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheData''))))]) in
guard g s"

definition n_NI_Remote_Get_Put_Home::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Get_Put_Home  dst\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Proc'')) (Const (index dst)))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState'')) (Const CACHE_E))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState''), (Const CACHE_S))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd''), (Const UNI_Put))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Data''), (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheData''))))]) in
guard g s"

definition n_NI_Local_GetX_Nak__part__0::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_Nak__part__0  src\<equiv>
let g = (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Nak)))]) in
guard g s"

definition n_NI_Local_GetX_Nak__part__1::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_Nak__part__1  src\<equiv>
let g = (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false)))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Nak)))]) in
guard g s"

definition n_NI_Local_GetX_Nak__part__2::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_Nak__part__2  src\<equiv>
let g = (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Nak)))]) in
guard g s"

definition n_NI_Local_GetX_GetX__part__0::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_GetX__part__0  src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_GetX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Proc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''))))]) in
guard g s"

definition n_NI_Local_GetX_GetX__part__1::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_GetX__part__1  src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src))))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_GetX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Proc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''))))]) in
guard g s"

definition n_NI_Local_GetX_PutX_1::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_1 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (Const false))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const true)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_2::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_2 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get)))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (Const false))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_3::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_3 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (Const false))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_4::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_4 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (forallForm (down N) (\<lambda>p. (orForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const false)) (eqn (Const (index p)) (Const (index src))))))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (Const false))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const true)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_5::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_5 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get)))) (forallForm (down N) (\<lambda>p. (orForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const false)) (eqn (Const (index p)) (Const (index src))))))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (Const false))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_6::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_6 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (forallForm (down N) (\<lambda>p. (orForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const false)) (eqn (Const (index p)) (Const (index src))))))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (Const false))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_7__part__0::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_7__part__0 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_7__part__1::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_7__part__1 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get)))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src))))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_7_NODE_Get__part__0::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_7_NODE_Get__part__0 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const true)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_7_NODE_Get__part__1::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_7_NODE_Get__part__1 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src))))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const true)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_8_Home::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_8_Home N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get)))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_8_Home_NODE_Get::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_8_Home_NODE_Get N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const true)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_8::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_8 N src pp\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') pp)) (Const true))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get)))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_8_NODE_Get::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_8_NODE_Get N src pp\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') pp)) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const true)))]) in
guard g s"

definition n_NI_Local_GetX_PutX_9__part__0::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_9__part__0 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData''))))]) in
guard g s"

definition n_NI_Local_GetX_PutX_9__part__1::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_9__part__1 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src))))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData''))))]) in
guard g s"

definition n_NI_Local_GetX_PutX_10_Home::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_10_Home N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData''))))]) in
guard g s"

definition n_NI_Local_GetX_PutX_10::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_10 N src pp\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index src)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') pp)) (Const true))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (andForm (neg (eqn (Const (index p)) (Const (index src)))) (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p)))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false))))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Ident ''Sta'') ''MemData''))))]) in
guard g s"

definition n_NI_Local_GetX_PutX_11::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Local_GetX_PutX_11 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const true))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (Const false))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I)))]) in
guard g s"

definition n_NI_Remote_GetX_Nak::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak  src dst\<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Proc'')) (Const (index dst)))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState'')) (Const CACHE_E)))) (neg (eqn (Const (index src)) (Const (index dst))))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_Nak))), (assign ((Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd''), (Const NAKC_Nakc)))]) in
guard g s"

definition n_NI_Remote_GetX_Nak_Home::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_Nak_Home  dst\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Proc'')) (Const (index dst)))) (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState'')) (Const CACHE_E)))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd''), (Const UNI_Nak))), (assign ((Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd''), (Const NAKC_Nakc)))]) in
guard g s"

definition n_NI_Remote_GetX_PutX::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX  src dst\<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Proc'')) (Const (index dst)))) (neg (eqn (Const (index src)) (Const (index dst))))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState''), (Const CACHE_I))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Cmd''), (Const UNI_PutX))), (assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') src) ''Data''), (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheData'')))), (assign ((Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd''), (Const SHWB_FAck))), (assign ((Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Proc''), (Const (index src)))), (assign ((Field (Field (Ident ''Sta'') ''ShWbMsg'') ''HomeProc''), (Const false)))]) in
guard g s"

definition n_NI_Remote_GetX_PutX_Home::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_GetX_PutX_Home  dst\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Proc'')) (Const (index dst)))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState'')) (Const CACHE_E))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState''), (Const CACHE_I))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd''), (Const UNI_PutX))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Data''), (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheData''))))]) in
guard g s"

definition n_NI_Remote_Put::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_Put  dst\<equiv>
let g = (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') dst) ''Cmd'')) (Const UNI_Put)) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') dst) ''Cmd''), (Const UNI_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''ProcCmd''), (Const NODE_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheData''), (iteForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''InvMarked'')) (Const true)) (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheData'')) (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') dst) ''Data''))))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState''), (iteForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''InvMarked'')) (Const true)) (Const CACHE_I) (Const CACHE_S)))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''InvMarked''), (iteForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''InvMarked'')) (Const true)) (Const false) (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''InvMarked'')))))]) in
guard g s"

definition n_NI_Remote_PutX::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Remote_PutX  dst\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''ProcCmd'')) (Const NODE_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') dst) ''Cmd'')) (Const UNI_PutX))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''UniMsg'') dst) ''Cmd''), (Const UNI_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''ProcCmd''), (Const NODE_None))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''InvMarked''), (Const false))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState''), (Const CACHE_E))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheData''), (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') dst) ''Data''))))]) in
guard g s"

definition n_NI_Inv::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Inv  dst\<equiv>
let g = (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''InvMsg'') dst) ''Cmd'')) (Const INV_Inv)) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') dst) ''Cmd''), (Const INV_InvAck))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''CacheState''), (Const CACHE_I))), (assign ((Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''InvMarked''), (iteForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''ProcCmd'')) (Const NODE_Get)) (Const true) (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') dst) ''InvMarked'')))))]) in
guard g s"

definition n_NI_InvAck_exists_Home::"nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_exists_Home  src\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src)) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''InvMsg'') src) ''Cmd'')) (Const INV_InvAck))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') src) ''Cmd''), (Const INV_None))), (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src), (Const false)))]) in
guard g s"

definition n_NI_InvAck_exists::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_exists  src pp\<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') pp)) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src)) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''InvMsg'') src) ''Cmd'')) (Const INV_InvAck))) (neg (eqn (Const (index pp)) (Const (index src))))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') src) ''Cmd''), (Const INV_None))), (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src), (Const false)))]) in
guard g s"

definition n_NI_InvAck_1::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_1 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src)) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''InvMsg'') src) ''Cmd'')) (Const INV_InvAck))) (forallForm (down N) (\<lambda>p. (orForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p)) (Const false)) (eqn (Const (index p)) (Const (index src))))))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') src) ''Cmd''), (Const INV_None))), (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false)))]) in
guard g s"

definition n_NI_InvAck_2::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_2 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet'')) (Const false)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src)) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''InvMsg'') src) ''Cmd'')) (Const INV_InvAck))) (forallForm (down N) (\<lambda>p. (orForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p)) (Const false)) (eqn (Const (index p)) (Const (index src))))))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') src) ''Cmd''), (Const INV_None))), (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const false)))]) in
guard g s"

definition n_NI_InvAck_3::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_NI_InvAck_3 N src\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src)) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''InvMsg'') src) ''Cmd'')) (Const INV_InvAck))) (forallForm (down N) (\<lambda>p. (orForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p)) (Const false)) (eqn (Const (index p)) (Const (index src))))))) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') src) ''Cmd''), (Const INV_None))), (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const false)))]) in
guard g s"

definition n_NI_Replace::"nat \<Rightarrow> rule" where [simp]:
"n_NI_Replace  src\<equiv>
let g = (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd'')) (Const RP_Replace)) in
let s = (parallelList [(assign ((Field (Para (Field (Ident ''Sta'') ''RpMsg'') src) ''Cmd''), (Const RP_None))), (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (Const false) (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') src))))), (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') src), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (Const false) (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') src)))))]) in
guard g s"

definition n_PI_Local_Get_Get::"rule" where [simp]:
"n_PI_Local_Get_Get  \<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_I))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_Get))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd''), (Const UNI_Get))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Proc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''HomeProc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''))))]) in
guard g s"

definition n_PI_Local_Get_Put::"rule" where [simp]:
"n_PI_Local_Get_Put  \<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_I))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked'')) (Const true)) (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData'')) (IVar (Field (Ident ''Sta'') ''MemData''))))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked'')) (Const true)) (Const CACHE_I) (Const CACHE_S)))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked'')) (Const true)) (Const false) (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked'')))))]) in
guard g s"

definition n_PI_Local_GetX_GetX__part__0::"rule" where [simp]:
"n_PI_Local_GetX_GetX__part__0  \<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_I))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_GetX))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd''), (Const UNI_GetX))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Proc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''HomeProc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''))))]) in
guard g s"

definition n_PI_Local_GetX_GetX__part__1::"rule" where [simp]:
"n_PI_Local_GetX_GetX__part__1  \<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_S))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_GetX))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd''), (Const UNI_GetX))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Proc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''HomeProc''), (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''))))]) in
guard g s"

definition n_PI_Local_GetX_PutX_HeadVld__part__0::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Local_GetX_PutX_HeadVld__part__0 N \<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_I))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false)))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false)))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_E))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData''), (IVar (Field (Ident ''Sta'') ''MemData''))))]) in
guard g s"

definition n_PI_Local_GetX_PutX_HeadVld__part__1::"nat \<Rightarrow> rule" where [simp]:
"n_PI_Local_GetX_PutX_HeadVld__part__1 N \<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_S))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const false))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (Const false))))), (forallSent (down N) (\<lambda>p. (assign ((Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd''), (iteForm (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false)))) (Const INV_Inv) (Const INV_None)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (orForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const false)))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd''), (Const INV_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_E))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData''), (IVar (Field (Ident ''Sta'') ''MemData''))))]) in
guard g s"

definition n_PI_Local_GetX_PutX__part__0::"rule" where [simp]:
"n_PI_Local_GetX_PutX__part__0  \<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_I))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_E))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData''), (IVar (Field (Ident ''Sta'') ''MemData''))))]) in
guard g s"

definition n_PI_Local_GetX_PutX__part__1::"rule" where [simp]:
"n_PI_Local_GetX_PutX__part__1  \<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_S))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_E))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData''), (IVar (Field (Ident ''Sta'') ''MemData''))))]) in
guard g s"

definition n_PI_Local_PutX::"rule" where [simp]:
"n_PI_Local_PutX  \<equiv>
let g = (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true)) (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false)))), (assign ((Field (Ident ''Sta'') ''MemData''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true)) (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData'')) (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData''))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true)) (Const false) (Const false)))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true)) (Const CACHE_I) (Const CACHE_I))))]) in
guard g s"

definition n_PI_Local_Replace::"rule" where [simp]:
"n_PI_Local_Replace  \<equiv>
let g = (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_S)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_I)))]) in
guard g s"

definition n_NI_Nak_Home::"rule" where [simp]:
"n_NI_Nak_Home  \<equiv>
let g = (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Nak)) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd''), (Const UNI_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const false)))]) in
guard g s"

definition n_NI_Nak_Clear::"rule" where [simp]:
"n_NI_Nak_Clear  \<equiv>
let g = (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc)) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd''), (Const NAKC_None))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const false)))]) in
guard g s"

definition n_NI_Local_Put::"rule" where [simp]:
"n_NI_Local_Put  \<equiv>
let g = (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd''), (Const UNI_None))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const true))), (assign ((Field (Ident ''Sta'') ''MemData''), (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Data'')))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked'')) (Const true)) (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData'')) (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Data''))))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked'')) (Const true)) (Const CACHE_I) (Const CACHE_S)))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked'')) (Const true)) (Const false) (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked'')))))]) in
guard g s"

definition n_NI_Local_PutXAcksDone::"rule" where [simp]:
"n_NI_Local_PutXAcksDone  \<equiv>
let g = (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd''), (Const UNI_None))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Local''), (Const true))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd''), (Const NODE_None))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState''), (Const CACHE_E))), (assign ((Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData''), (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Data''))))]) in
guard g s"

definition n_NI_Wb::"rule" where [simp]:
"n_NI_Wb  \<equiv>
let g = (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb)) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd''), (Const WB_None))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld''), (Const false))), (assign ((Field (Ident ''Sta'') ''MemData''), (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Data''))))]) in
guard g s"

definition n_NI_FAck::"rule" where [simp]:
"n_NI_FAck  \<equiv>
let g = (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck)) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd''), (Const SHWB_None))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''HomeProc'')) (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr''))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Proc'')) (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')))))]) in
guard g s"

definition n_NI_ShWb::"nat \<Rightarrow> rule" where [simp]:
"n_NI_ShWb N \<equiv>
let g = (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd''), (Const SHWB_None))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Pending''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''Dirty''), (Const false))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld''), (Const true))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p), (iteForm (orForm (andForm (eqn (Const (index p)) (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Proc''))) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''HomeProc'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (Const true) (Const false)))))), (forallSent (down N) (\<lambda>p. (assign ((Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p), (iteForm (orForm (andForm (eqn (Const (index p)) (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Proc''))) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''HomeProc'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const true))) (Const true) (Const false)))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (iteForm (orForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''HomeProc'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')) (Const true))) (Const true) (Const false)))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (iteForm (orForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''HomeProc'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')) (Const true))) (Const true) (Const false)))), (assign ((Field (Ident ''Sta'') ''MemData''), (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Data''))))]) in
guard g s"

definition n_NI_Replace_Home::"rule" where [simp]:
"n_NI_Replace_Home  \<equiv>
let g = (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeRpMsg'') ''Cmd'')) (Const RP_Replace)) in
let s = (parallelList [(assign ((Field (Field (Ident ''Sta'') ''HomeRpMsg'') ''Cmd''), (Const RP_None))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (Const false) (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet''))))), (assign ((Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet''), (iteForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (Const false) (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')))))]) in
guard g s"

subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> src data. src\<le>N\<and>data\<le>N\<and>r=n_Store  src data) \<or>
(\<exists> data. data\<le>N\<and>r=n_Store_Home  data) \<or>
(\<exists> src. src\<le>N\<and>r=n_PI_Remote_Get  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_PI_Remote_GetX  src) \<or>
(\<exists> dst. dst\<le>N\<and>r=n_PI_Remote_PutX  dst) \<or>
(\<exists> src. src\<le>N\<and>r=n_PI_Remote_Replace  src) \<or>
(\<exists> dst. dst\<le>N\<and>r=n_NI_Nak  dst) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_Get_Nak__part__0  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_Get_Nak__part__1  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_Get_Nak__part__2  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_Get_Get__part__0  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_Get_Get__part__1  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_Get_Put_Head N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_Get_Put  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_Get_Put_Dirty  src) \<or>
(\<exists> src dst. src\<le>N\<and>dst\<le>N\<and>src~=dst\<and>r=n_NI_Remote_Get_Nak  src dst) \<or>
(\<exists> dst. dst\<le>N\<and>r=n_NI_Remote_Get_Nak_Home  dst) \<or>
(\<exists> src dst. src\<le>N\<and>dst\<le>N\<and>src~=dst\<and>r=n_NI_Remote_Get_Put  src dst) \<or>
(\<exists> dst. dst\<le>N\<and>r=n_NI_Remote_Get_Put_Home  dst) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_Nak__part__0  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_Nak__part__1  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_Nak__part__2  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_GetX__part__0  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_GetX__part__1  src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_1 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_2 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_3 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_4 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_5 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_6 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_7__part__0 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_7__part__1 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_7_NODE_Get__part__0 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_7_NODE_Get__part__1 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_8_Home N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_8_Home_NODE_Get N src) \<or>
(\<exists> src pp. src\<le>N\<and>pp\<le>N\<and>src~=pp\<and>r=n_NI_Local_GetX_PutX_8 N src pp) \<or>
(\<exists> src pp. src\<le>N\<and>pp\<le>N\<and>src~=pp\<and>r=n_NI_Local_GetX_PutX_8_NODE_Get N src pp) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_9__part__0 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_9__part__1 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_10_Home N src) \<or>
(\<exists> src pp. src\<le>N\<and>pp\<le>N\<and>src~=pp\<and>r=n_NI_Local_GetX_PutX_10 N src pp) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Local_GetX_PutX_11 N src) \<or>
(\<exists> src dst. src\<le>N\<and>dst\<le>N\<and>src~=dst\<and>r=n_NI_Remote_GetX_Nak  src dst) \<or>
(\<exists> dst. dst\<le>N\<and>r=n_NI_Remote_GetX_Nak_Home  dst) \<or>
(\<exists> src dst. src\<le>N\<and>dst\<le>N\<and>src~=dst\<and>r=n_NI_Remote_GetX_PutX  src dst) \<or>
(\<exists> dst. dst\<le>N\<and>r=n_NI_Remote_GetX_PutX_Home  dst) \<or>
(\<exists> dst. dst\<le>N\<and>r=n_NI_Remote_Put  dst) \<or>
(\<exists> dst. dst\<le>N\<and>r=n_NI_Remote_PutX  dst) \<or>
(\<exists> dst. dst\<le>N\<and>r=n_NI_Inv  dst) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_InvAck_exists_Home  src) \<or>
(\<exists> src pp. src\<le>N\<and>pp\<le>N\<and>src~=pp\<and>r=n_NI_InvAck_exists  src pp) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_InvAck_1 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_InvAck_2 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_InvAck_3 N src) \<or>
(\<exists> src. src\<le>N\<and>r=n_NI_Replace  src) \<or>
(r=n_PI_Local_Get_Get  ) \<or>
(r=n_PI_Local_Get_Put  ) \<or>
(r=n_PI_Local_GetX_GetX__part__0  ) \<or>
(r=n_PI_Local_GetX_GetX__part__1  ) \<or>
(r=n_PI_Local_GetX_PutX_HeadVld__part__0 N ) \<or>
(r=n_PI_Local_GetX_PutX_HeadVld__part__1 N ) \<or>
(r=n_PI_Local_GetX_PutX__part__0  ) \<or>
(r=n_PI_Local_GetX_PutX__part__1  ) \<or>
(r=n_PI_Local_PutX  ) \<or>
(r=n_PI_Local_Replace  ) \<or>
(r=n_NI_Nak_Home  ) \<or>
(r=n_NI_Nak_Clear  ) \<or>
(r=n_NI_Local_Put  ) \<or>
(r=n_NI_Local_PutXAcksDone  ) \<or>
(r=n_NI_Wb  ) \<or>
(r=n_NI_FAck  ) \<or>
(r=n_NI_ShWb N ) \<or>
(r=n_NI_Replace_Home  )
}"



subsection{*Definitions of a Formally Parameterized Invariant Formulas*}

definition inv__1::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__1 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv3) ''CacheState'')) (Const CACHE_E))))"

definition inv__2::"nat \<Rightarrow> formula" where [simp]:
"inv__2 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))))"

definition inv__3::"formula" where [simp]:
"inv__3  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (neg (eqn (IVar (Field (Ident ''Sta'') ''MemData'')) (IVar (Field (Ident ''Sta'') ''CurrData''))))))"

definition inv__4::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__4 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''Cmd'')) (Const UNI_PutX))))"

definition inv__5::"nat \<Rightarrow> formula" where [simp]:
"inv__5 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX))))"

definition inv__6::"nat \<Rightarrow> formula" where [simp]:
"inv__6 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false))))"

definition inv__7::"nat \<Rightarrow> formula" where [simp]:
"inv__7 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX))))"

definition inv__8::"formula" where [simp]:
"inv__8  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))))"

definition inv__9::"formula" where [simp]:
"inv__9  \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData'')) (IVar (Field (Ident ''Sta'') ''CurrData'')))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))))"

definition inv__10::"formula" where [simp]:
"inv__10  \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData'')) (IVar (Field (Ident ''Sta'') ''CurrData'')))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))))"

definition inv__11::"formula" where [simp]:
"inv__11  \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Data'')) (IVar (Field (Ident ''Sta'') ''CurrData'')))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put))))"

definition inv__12::"formula" where [simp]:
"inv__12  \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Data'')) (IVar (Field (Ident ''Sta'') ''CurrData'')))) (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb))))"

definition inv__13::"formula" where [simp]:
"inv__13  \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Data'')) (IVar (Field (Ident ''Sta'') ''CurrData'')))) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb))))"

definition inv__14::"formula" where [simp]:
"inv__14  \<equiv>
(neg (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')) (Const true)))"

definition inv__15::"nat \<Rightarrow> formula" where [simp]:
"inv__15 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))))"

definition inv__16::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__16 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''Cmd'')) (Const UNI_PutX))))"

definition inv__17::"nat \<Rightarrow> formula" where [simp]:
"inv__17 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false))))"

definition inv__18::"nat \<Rightarrow> formula" where [simp]:
"inv__18 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX))))"

definition inv__19::"nat \<Rightarrow> formula" where [simp]:
"inv__19 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put))))"

definition inv__20::"nat \<Rightarrow> formula" where [simp]:
"inv__20 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb))))"

definition inv__21::"nat \<Rightarrow> formula" where [simp]:
"inv__21 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb))))"

definition inv__22::"formula" where [simp]:
"inv__22  \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Data'')) (IVar (Field (Ident ''Sta'') ''CurrData'')))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX))))"

definition inv__23::"formula" where [simp]:
"inv__23  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))))"

definition inv__24::"nat \<Rightarrow> formula" where [simp]:
"inv__24 p__Inv4 \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheData'')) (IVar (Field (Ident ''Sta'') ''CurrData'')))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E))))"

definition inv__25::"formula" where [simp]:
"inv__25  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))))"

definition inv__26::"formula" where [simp]:
"inv__26  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))))"

definition inv__27::"formula" where [simp]:
"inv__27  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX))))"

definition inv__28::"formula" where [simp]:
"inv__28  \<equiv>
(neg (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked'')) (Const true)))"

definition inv__29::"formula" where [simp]:
"inv__29  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''HomeProc'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb))))"

definition inv__30::"nat \<Rightarrow> formula" where [simp]:
"inv__30 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX))))"

definition inv__31::"nat \<Rightarrow> formula" where [simp]:
"inv__31 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E))))"

definition inv__32::"nat \<Rightarrow> formula" where [simp]:
"inv__32 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put))))"

definition inv__33::"nat \<Rightarrow> formula" where [simp]:
"inv__33 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb))))"

definition inv__34::"nat \<Rightarrow> formula" where [simp]:
"inv__34 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb))))"

definition inv__35::"formula" where [simp]:
"inv__35  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))))"

definition inv__36::"formula" where [simp]:
"inv__36  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E))))"

definition inv__37::"formula" where [simp]:
"inv__37  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get))))"

definition inv__38::"formula" where [simp]:
"inv__38  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false))))"

definition inv__39::"nat \<Rightarrow> formula" where [simp]:
"inv__39 p__Inv4 \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Data'')) (IVar (Field (Ident ''Sta'') ''CurrData'')))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX))))"

definition inv__40::"formula" where [simp]:
"inv__40  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false))))"

definition inv__41::"formula" where [simp]:
"inv__41  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX))))"

definition inv__42::"formula" where [simp]:
"inv__42  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false))))"

definition inv__43::"formula" where [simp]:
"inv__43  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX))))"

definition inv__44::"formula" where [simp]:
"inv__44  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))))"

definition inv__45::"formula" where [simp]:
"inv__45  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_Get))))"

definition inv__46::"formula" where [simp]:
"inv__46  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true))))"

definition inv__47::"formula" where [simp]:
"inv__47  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))))"

definition inv__48::"formula" where [simp]:
"inv__48  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))))"

definition inv__49::"formula" where [simp]:
"inv__49  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))))"

definition inv__50::"formula" where [simp]:
"inv__50  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX))))"

definition inv__51::"formula" where [simp]:
"inv__51  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX))))"

definition inv__52::"formula" where [simp]:
"inv__52  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))))"

definition inv__53::"formula" where [simp]:
"inv__53  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))))"

definition inv__54::"formula" where [simp]:
"inv__54  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb))))"

definition inv__55::"formula" where [simp]:
"inv__55  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb))))"

definition inv__56::"formula" where [simp]:
"inv__56  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb))))"

definition inv__57::"formula" where [simp]:
"inv__57  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))))"

definition inv__58::"formula" where [simp]:
"inv__58  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX))))"

definition inv__59::"formula" where [simp]:
"inv__59  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX))))"

definition inv__60::"nat \<Rightarrow> formula" where [simp]:
"inv__60 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true))))"

definition inv__61::"formula" where [simp]:
"inv__61  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc))))"

definition inv__62::"formula" where [simp]:
"inv__62  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck))))"

definition inv__63::"formula" where [simp]:
"inv__63  \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_I))))"

definition inv__64::"formula" where [simp]:
"inv__64  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''HomeProc'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck))))"

definition inv__65::"formula" where [simp]:
"inv__65  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get))))"

definition inv__66::"formula" where [simp]:
"inv__66  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_S))))"

definition inv__67::"nat \<Rightarrow> formula" where [simp]:
"inv__67 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true))))"

definition inv__68::"formula" where [simp]:
"inv__68  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc))))"

definition inv__69::"formula" where [simp]:
"inv__69  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck))))"

definition inv__70::"formula" where [simp]:
"inv__70  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb))))"

definition inv__71::"nat \<Rightarrow> formula" where [simp]:
"inv__71 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true))))"

definition inv__72::"formula" where [simp]:
"inv__72  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc))))"

definition inv__73::"formula" where [simp]:
"inv__73  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck))))"

definition inv__74::"nat \<Rightarrow> formula" where [simp]:
"inv__74 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__75::"nat \<Rightarrow> formula" where [simp]:
"inv__75 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true))))"

definition inv__76::"formula" where [simp]:
"inv__76  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc))))"

definition inv__77::"nat \<Rightarrow> formula" where [simp]:
"inv__77 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__78::"nat \<Rightarrow> formula" where [simp]:
"inv__78 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true))))"

definition inv__79::"formula" where [simp]:
"inv__79  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc))))"

definition inv__80::"formula" where [simp]:
"inv__80  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck))))"

definition inv__81::"nat \<Rightarrow> formula" where [simp]:
"inv__81 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true))))"

definition inv__82::"formula" where [simp]:
"inv__82  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true))))"

definition inv__83::"nat \<Rightarrow> formula" where [simp]:
"inv__83 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__84::"nat \<Rightarrow> formula" where [simp]:
"inv__84 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_PutX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__85::"formula" where [simp]:
"inv__85  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_S)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))))"

definition inv__86::"nat \<Rightarrow> formula" where [simp]:
"inv__86 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true))))"

definition inv__87::"formula" where [simp]:
"inv__87  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true))))"

definition inv__88::"nat \<Rightarrow> formula" where [simp]:
"inv__88 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))))"

definition inv__89::"nat \<Rightarrow> formula" where [simp]:
"inv__89 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__90::"nat \<Rightarrow> formula" where [simp]:
"inv__90 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__91::"formula" where [simp]:
"inv__91  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))))"

definition inv__92::"formula" where [simp]:
"inv__92  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))))"

definition inv__93::"nat \<Rightarrow> formula" where [simp]:
"inv__93 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true))))"

definition inv__94::"formula" where [simp]:
"inv__94  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true))))"

definition inv__95::"nat \<Rightarrow> formula" where [simp]:
"inv__95 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__96::"nat \<Rightarrow> formula" where [simp]:
"inv__96 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_Put)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__97::"nat \<Rightarrow> formula" where [simp]:
"inv__97 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true))))"

definition inv__98::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__98 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''HomeProc'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true))))"

definition inv__99::"nat \<Rightarrow> formula" where [simp]:
"inv__99 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc))))"

definition inv__100::"nat \<Rightarrow> formula" where [simp]:
"inv__100 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck))))"

definition inv__101::"nat \<Rightarrow> formula" where [simp]:
"inv__101 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb))))"

definition inv__102::"nat \<Rightarrow> formula" where [simp]:
"inv__102 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true))))"

definition inv__103::"nat \<Rightarrow> formula" where [simp]:
"inv__103 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E))))"

definition inv__104::"formula" where [simp]:
"inv__104  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true))))"

definition inv__105::"nat \<Rightarrow> formula" where [simp]:
"inv__105 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__106::"nat \<Rightarrow> formula" where [simp]:
"inv__106 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true))))"

definition inv__107::"formula" where [simp]:
"inv__107  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true))))"

definition inv__108::"nat \<Rightarrow> formula" where [simp]:
"inv__108 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__109::"nat \<Rightarrow> formula" where [simp]:
"inv__109 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E))))"

definition inv__110::"nat \<Rightarrow> formula" where [simp]:
"inv__110 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E))))"

definition inv__111::"formula" where [simp]:
"inv__111  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_S)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const true))))"

definition inv__112::"nat \<Rightarrow> formula" where [simp]:
"inv__112 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true))))"

definition inv__113::"formula" where [simp]:
"inv__113  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const true))))"

definition inv__114::"nat \<Rightarrow> formula" where [simp]:
"inv__114 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false))))"

definition inv__115::"nat \<Rightarrow> formula" where [simp]:
"inv__115 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc))))"

definition inv__116::"nat \<Rightarrow> formula" where [simp]:
"inv__116 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck))))"

definition inv__117::"nat \<Rightarrow> formula" where [simp]:
"inv__117 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))))"

definition inv__118::"formula" where [simp]:
"inv__118  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck))))"

definition inv__119::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__119 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__120::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__120 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__121::"nat \<Rightarrow> formula" where [simp]:
"inv__121 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true))))"

definition inv__122::"formula" where [simp]:
"inv__122  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true))))"

definition inv__123::"nat \<Rightarrow> formula" where [simp]:
"inv__123 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true))))"

definition inv__124::"nat \<Rightarrow> formula" where [simp]:
"inv__124 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p__Inv4)))))"

definition inv__125::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__125 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv3)) (Const true))))"

definition inv__126::"nat \<Rightarrow> formula" where [simp]:
"inv__126 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_Get)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))))"

definition inv__127::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__127 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv3)) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E))))"

definition inv__128::"nat \<Rightarrow> formula" where [simp]:
"inv__128 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E))))"

definition inv__129::"nat \<Rightarrow> formula" where [simp]:
"inv__129 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true))))"

definition inv__130::"nat \<Rightarrow> formula" where [simp]:
"inv__130 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX))))"

definition inv__131::"nat \<Rightarrow> formula" where [simp]:
"inv__131 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true))))"

definition inv__132::"nat \<Rightarrow> formula" where [simp]:
"inv__132 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false))))"

definition inv__133::"formula" where [simp]:
"inv__133  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false))))"

definition inv__134::"nat \<Rightarrow> formula" where [simp]:
"inv__134 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb))))"

definition inv__135::"formula" where [simp]:
"inv__135  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb))))"

definition inv__136::"nat \<Rightarrow> formula" where [simp]:
"inv__136 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc))))"

definition inv__137::"formula" where [simp]:
"inv__137  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true))))"

definition inv__138::"formula" where [simp]:
"inv__138  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))))"

definition inv__139::"nat \<Rightarrow> formula" where [simp]:
"inv__139 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__140::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__140 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv3)) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__141::"nat \<Rightarrow> formula" where [simp]:
"inv__141 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck))))"

definition inv__142::"formula" where [simp]:
"inv__142  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true))))"

definition inv__143::"formula" where [simp]:
"inv__143  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true))))"

definition inv__144::"nat \<Rightarrow> formula" where [simp]:
"inv__144 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_Nakc))))"

definition inv__145::"nat \<Rightarrow> formula" where [simp]:
"inv__145 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_FAck))))"

definition inv__146::"formula" where [simp]:
"inv__146  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_ShWb))))"

definition inv__147::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__147 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''Cmd'')) (Const UNI_PutX))))"

definition inv__148::"nat \<Rightarrow> formula" where [simp]:
"inv__148 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX))))"

definition inv__149::"nat \<Rightarrow> formula" where [simp]:
"inv__149 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX))))"

definition inv__150::"nat \<Rightarrow> formula" where [simp]:
"inv__150 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX))))"

definition inv__151::"nat \<Rightarrow> formula" where [simp]:
"inv__151 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb))))"

definition inv__152::"formula" where [simp]:
"inv__152  \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_Wb))))"

definition inv__153::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__153 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv3)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E))))"

definition inv__154::"nat \<Rightarrow> formula" where [simp]:
"inv__154 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p__Inv4) ''CacheState'')) (Const CACHE_E))))"

definition inv__155::"nat \<Rightarrow> formula" where [simp]:
"inv__155 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__156::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__156 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p__Inv3)) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__157::"nat \<Rightarrow> formula" where [simp]:
"inv__157 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__158::"nat \<Rightarrow> formula" where [simp]:
"inv__158 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const true)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__159::"nat \<Rightarrow> formula" where [simp]:
"inv__159 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index p__Inv4)))))"

definition inv__160::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__160 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (andForm (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''Cmd'')) (Const UNI_GetX)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''HomeProc'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_GetX))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''HomeProc'')) (Const false))))"

definition inv__161::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__161 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv3) ''Cmd'')) (Const UNI_PutX))))"

definition inv__162::"nat \<Rightarrow> formula" where [simp]:
"inv__162 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false)) (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p__Inv4) ''Cmd'')) (Const UNI_PutX))))"

subsection{*Definitions of  the Set of Invariant Formula Instances in a $N$-protocol Instance*}
definition invariants::"nat \<Rightarrow> formula set" where [simp]:
"invariants N \<equiv> {f.
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__2  p__Inv4) \<or>
(f=inv__3  ) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__4  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__5  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__6  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__7  p__Inv4) \<or>
(f=inv__8  ) \<or>
(f=inv__9  ) \<or>
(f=inv__10  ) \<or>
(f=inv__11  ) \<or>
(f=inv__12  ) \<or>
(f=inv__13  ) \<or>
(f=inv__14  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__15  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__16  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__17  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__18  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__19  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__20  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__21  p__Inv4) \<or>
(f=inv__22  ) \<or>
(f=inv__23  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__24  p__Inv4) \<or>
(f=inv__25  ) \<or>
(f=inv__26  ) \<or>
(f=inv__27  ) \<or>
(f=inv__28  ) \<or>
(f=inv__29  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__30  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__31  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__32  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__33  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__34  p__Inv4) \<or>
(f=inv__35  ) \<or>
(f=inv__36  ) \<or>
(f=inv__37  ) \<or>
(f=inv__38  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__39  p__Inv4) \<or>
(f=inv__40  ) \<or>
(f=inv__41  ) \<or>
(f=inv__42  ) \<or>
(f=inv__43  ) \<or>
(f=inv__44  ) \<or>
(f=inv__45  ) \<or>
(f=inv__46  ) \<or>
(f=inv__47  ) \<or>
(f=inv__48  ) \<or>
(f=inv__49  ) \<or>
(f=inv__50  ) \<or>
(f=inv__51  ) \<or>
(f=inv__52  ) \<or>
(f=inv__53  ) \<or>
(f=inv__54  ) \<or>
(f=inv__55  ) \<or>
(f=inv__56  ) \<or>
(f=inv__57  ) \<or>
(f=inv__58  ) \<or>
(f=inv__59  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__60  p__Inv4) \<or>
(f=inv__61  ) \<or>
(f=inv__62  ) \<or>
(f=inv__63  ) \<or>
(f=inv__64  ) \<or>
(f=inv__65  ) \<or>
(f=inv__66  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__67  p__Inv4) \<or>
(f=inv__68  ) \<or>
(f=inv__69  ) \<or>
(f=inv__70  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__71  p__Inv4) \<or>
(f=inv__72  ) \<or>
(f=inv__73  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__74  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__75  p__Inv4) \<or>
(f=inv__76  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__77  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__78  p__Inv4) \<or>
(f=inv__79  ) \<or>
(f=inv__80  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__81  p__Inv4) \<or>
(f=inv__82  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__83  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__84  p__Inv4) \<or>
(f=inv__85  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__86  p__Inv4) \<or>
(f=inv__87  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__88  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__89  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__90  p__Inv4) \<or>
(f=inv__91  ) \<or>
(f=inv__92  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__93  p__Inv4) \<or>
(f=inv__94  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__95  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__96  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__97  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__98  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__99  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__100  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__101  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__102  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__103  p__Inv4) \<or>
(f=inv__104  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__105  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__106  p__Inv4) \<or>
(f=inv__107  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__108  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__109  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__110  p__Inv4) \<or>
(f=inv__111  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__112  p__Inv4) \<or>
(f=inv__113  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__114  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__115  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__116  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__117  p__Inv4) \<or>
(f=inv__118  ) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__119  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__120  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__121  p__Inv4) \<or>
(f=inv__122  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__123  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__124  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__125  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__126  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__127  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__128  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__129  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__130  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__131  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__132  p__Inv4) \<or>
(f=inv__133  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__134  p__Inv4) \<or>
(f=inv__135  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__136  p__Inv4) \<or>
(f=inv__137  ) \<or>
(f=inv__138  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__139  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__140  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__141  p__Inv4) \<or>
(f=inv__142  ) \<or>
(f=inv__143  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__144  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__145  p__Inv4) \<or>
(f=inv__146  ) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__147  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__148  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__149  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__150  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__151  p__Inv4) \<or>
(f=inv__152  ) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__153  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__154  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__155  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__156  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__157  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__158  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__159  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__160  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__161  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__162  p__Inv4)
}"



subsection{*Definitions of initial states*}

definition initSpec0::"formula" where [simp]:
"initSpec0  \<equiv> (eqn (IVar (Field (Ident ''Sta'') ''MemData'')) (Const (index 1)))"

definition initSpec1::"formula" where [simp]:
"initSpec1  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Pending'')) (Const false))"

definition initSpec2::"formula" where [simp]:
"initSpec2  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Local'')) (Const false))"

definition initSpec3::"formula" where [simp]:
"initSpec3  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''Dirty'')) (Const false))"

definition initSpec4::"formula" where [simp]:
"initSpec4  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadVld'')) (Const false))"

definition initSpec5::"formula" where [simp]:
"initSpec5  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HeadPtr'')) (Const (index 1)))"

definition initSpec6::"formula" where [simp]:
"initSpec6  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeHeadPtr'')) (Const true))"

definition initSpec7::"formula" where [simp]:
"initSpec7  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''ShrVld'')) (Const false))"

definition initSpec8::"formula" where [simp]:
"initSpec8  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Cmd'')) (Const WB_None))"

definition initSpec9::"formula" where [simp]:
"initSpec9  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Proc'')) (Const (index 1)))"

definition initSpec10::"formula" where [simp]:
"initSpec10  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''HomeProc'')) (Const true))"

definition initSpec11::"formula" where [simp]:
"initSpec11  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''WbMsg'') ''Data'')) (Const (index 1)))"

definition initSpec12::"formula" where [simp]:
"initSpec12  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Cmd'')) (Const SHWB_None))"

definition initSpec13::"formula" where [simp]:
"initSpec13  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Proc'')) (Const (index 1)))"

definition initSpec14::"formula" where [simp]:
"initSpec14  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''HomeProc'')) (Const true))"

definition initSpec15::"formula" where [simp]:
"initSpec15  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''ShWbMsg'') ''Data'')) (Const (index 1)))"

definition initSpec16::"formula" where [simp]:
"initSpec16  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''NakcMsg'') ''Cmd'')) (Const NAKC_None))"

definition initSpec17::"nat \<Rightarrow> formula" where [simp]:
"initSpec17 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p) ''ProcCmd'')) (Const NODE_None))))"

definition initSpec18::"nat \<Rightarrow> formula" where [simp]:
"initSpec18 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p) ''InvMarked'')) (Const false))))"

definition initSpec19::"nat \<Rightarrow> formula" where [simp]:
"initSpec19 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p) ''CacheState'')) (Const CACHE_I))))"

definition initSpec20::"nat \<Rightarrow> formula" where [simp]:
"initSpec20 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''Proc'') p) ''CacheData'')) (Const (index 1)))))"

definition initSpec21::"nat \<Rightarrow> formula" where [simp]:
"initSpec21 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''ShrSet'') p)) (Const false))))"

definition initSpec22::"nat \<Rightarrow> formula" where [simp]:
"initSpec22 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Para (Field (Field (Ident ''Sta'') ''Dir'') ''InvSet'') p)) (Const false))))"

definition initSpec23::"nat \<Rightarrow> formula" where [simp]:
"initSpec23 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p) ''Cmd'')) (Const UNI_None))))"

definition initSpec24::"nat \<Rightarrow> formula" where [simp]:
"initSpec24 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p) ''Proc'')) (Const (index 1)))))"

definition initSpec25::"nat \<Rightarrow> formula" where [simp]:
"initSpec25 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p) ''HomeProc'')) (Const true))))"

definition initSpec26::"nat \<Rightarrow> formula" where [simp]:
"initSpec26 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''UniMsg'') p) ''Data'')) (Const (index 1)))))"

definition initSpec27::"nat \<Rightarrow> formula" where [simp]:
"initSpec27 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''InvMsg'') p) ''Cmd'')) (Const INV_None))))"

definition initSpec28::"nat \<Rightarrow> formula" where [simp]:
"initSpec28 N \<equiv> (forallForm (down N) (% p . (eqn (IVar (Field (Para (Field (Ident ''Sta'') ''RpMsg'') p) ''Cmd'')) (Const RP_None))))"

definition initSpec29::"formula" where [simp]:
"initSpec29  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''ProcCmd'')) (Const NODE_None))"

definition initSpec30::"formula" where [simp]:
"initSpec30  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''InvMarked'')) (Const false))"

definition initSpec31::"formula" where [simp]:
"initSpec31  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheState'')) (Const CACHE_I))"

definition initSpec32::"formula" where [simp]:
"initSpec32  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeProc'') ''CacheData'')) (Const (index 1)))"

definition initSpec33::"formula" where [simp]:
"initSpec33  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeShrSet'')) (Const false))"

definition initSpec34::"formula" where [simp]:
"initSpec34  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''Dir'') ''HomeInvSet'')) (Const false))"

definition initSpec35::"formula" where [simp]:
"initSpec35  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Cmd'')) (Const UNI_None))"

definition initSpec36::"formula" where [simp]:
"initSpec36  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Proc'')) (Const (index 1)))"

definition initSpec37::"formula" where [simp]:
"initSpec37  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''HomeProc'')) (Const true))"

definition initSpec38::"formula" where [simp]:
"initSpec38  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeUniMsg'') ''Data'')) (Const (index 1)))"

definition initSpec39::"formula" where [simp]:
"initSpec39  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeInvMsg'') ''Cmd'')) (Const INV_None))"

definition initSpec40::"formula" where [simp]:
"initSpec40  \<equiv> (eqn (IVar (Field (Field (Ident ''Sta'') ''HomeRpMsg'') ''Cmd'')) (Const RP_None))"

definition initSpec41::"formula" where [simp]:
"initSpec41  \<equiv> (eqn (IVar (Field (Ident ''Sta'') ''CurrData'')) (Const (index 1)))"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 ),
(initSpec1 ),
(initSpec2 ),
(initSpec3 ),
(initSpec4 ),
(initSpec5 ),
(initSpec6 ),
(initSpec7 ),
(initSpec8 ),
(initSpec9 ),
(initSpec10 ),
(initSpec11 ),
(initSpec12 ),
(initSpec13 ),
(initSpec14 ),
(initSpec15 ),
(initSpec16 ),
(initSpec17 N),
(initSpec18 N),
(initSpec19 N),
(initSpec20 N),
(initSpec21 N),
(initSpec22 N),
(initSpec23 N),
(initSpec24 N),
(initSpec25 N),
(initSpec26 N),
(initSpec27 N),
(initSpec28 N),
(initSpec29 ),
(initSpec30 ),
(initSpec31 ),
(initSpec32 ),
(initSpec33 ),
(initSpec34 ),
(initSpec35 ),
(initSpec36 ),
(initSpec37 ),
(initSpec38 ),
(initSpec39 ),
(initSpec40 ),
(initSpec41 )
]"

end
