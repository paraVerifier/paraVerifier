(*  Title:      HOL/Auth/n_german_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_german Protocol Case Study*} 

theory n_german_base imports paraTheory
begin

section{*Main definitions*}

subsection{* Definitions of Constants*}
definition I::"scalrValueType" where [simp]: "I\<equiv> enum ''control'' ''I''"
definition S::"scalrValueType" where [simp]: "S\<equiv> enum ''control'' ''S''"
definition E::"scalrValueType" where [simp]: "E\<equiv> enum ''control'' ''E''"
definition Empty::"scalrValueType" where [simp]: "Empty\<equiv> enum ''control'' ''Empty''"
definition ReqS::"scalrValueType" where [simp]: "ReqS\<equiv> enum ''control'' ''ReqS''"
definition ReqE::"scalrValueType" where [simp]: "ReqE\<equiv> enum ''control'' ''ReqE''"
definition Inv::"scalrValueType" where [simp]: "Inv\<equiv> enum ''control'' ''Inv''"
definition InvAck::"scalrValueType" where [simp]: "InvAck\<equiv> enum ''control'' ''InvAck''"
definition GntS::"scalrValueType" where [simp]: "GntS\<equiv> enum ''control'' ''GntS''"
definition GntE::"scalrValueType" where [simp]: "GntE\<equiv> enum ''control'' ''GntE''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"



subsection{*  Definitions of Parameterized Rules *}

definition n_SendReqS::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqS  j\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const I)) (eqn (IVar (Field (Para (Ident ''Chan1'') j) ''Cmd'')) (Const Empty))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan1'') j) ''Cmd''), (Const ReqS)))]) in
guard g s"

definition n_SendReqEI::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqEI  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I)) (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const ReqE)))]) in
guard g s"

definition n_SendReqES::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqES  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const S)) (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const ReqE)))]) in
guard g s"

definition n_RecvReq::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReq N i\<equiv>
let g = (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (neg (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty)))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')))), (assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const Empty))), (assign ((Ident ''CurPtr''), (Const (index i)))), (forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''InvSet'') j), (IVar (Para (Ident ''ShrSet'') j))))))]) in
guard g s"

definition n_SendInvE::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvE  i\<equiv>
let g = (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqE))) (eqn (IVar (Para (Ident ''InvSet'') i)) (Const true))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Inv))), (assign ((Para (Ident ''InvSet'') i), (Const false)))]) in
guard g s"

definition n_SendInvS::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvS  i\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (eqn (IVar (Para (Ident ''InvSet'') i)) (Const true))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Inv))), (assign ((Para (Ident ''InvSet'') i), (Const false)))]) in
guard g s"

definition n_SendInvAck::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvAck  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty))), (assign ((Field (Para (Ident ''Chan3'') i) ''Cmd''), (Const InvAck))), (assign ((Field (Para (Ident ''Chan3'') i) ''Data''), (iteForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) (IVar (Field (Para (Ident ''Cache'') i) ''Data'')) (IVar (Field (Para (Ident ''Chan3'') i) ''Data''))))), (assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const I)))]) in
guard g s"

definition n_RecvInvAck::"nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Ident ''CurCmd'')) (Const Empty)))) in
let s = (parallelList [(assign ((Para (Ident ''ShrSet'') i), (Const false))), (assign ((Ident ''MemData''), (iteForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (IVar (Field (Para (Ident ''Chan3'') i) ''Data'')) (IVar (Ident ''MemData''))))), (assign ((Ident ''ExGntd''), (iteForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (Const false) (IVar (Ident ''ExGntd''))))), (assign ((Field (Para (Ident ''Chan3'') i) ''Cmd''), (Const Empty)))]) in
guard g s"

definition n_SendGntS::"nat \<Rightarrow> rule" where [simp]:
"n_SendGntS  i\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (eqn (IVar (Ident ''CurPtr'')) (Const (index i)))) (eqn (IVar (Ident ''ExGntd'')) (Const false))) in
let s = (parallelList [(assign ((Para (Ident ''ShrSet'') i), (Const true))), (assign ((Ident ''CurCmd''), (Const Empty))), (assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const GntS))), (assign ((Field (Para (Ident ''Chan2'') i) ''Data''), (IVar (Ident ''MemData''))))]) in
guard g s"

definition n_SendGntE::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_SendGntE N i\<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqE))) (eqn (IVar (Ident ''CurPtr'')) (Const (index i)))) (eqn (IVar (Ident ''ExGntd'')) (Const false))) (forallForm (down N) (\<lambda>j. (eqn (IVar (Para (Ident ''ShrSet'') j)) (Const false))))) in
let s = (parallelList [(assign ((Para (Ident ''ShrSet'') i), (Const true))), (assign ((Ident ''CurCmd''), (Const Empty))), (assign ((Ident ''ExGntd''), (Const true))), (assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const GntE))), (assign ((Field (Para (Ident ''Chan2'') i) ''Data''), (IVar (Ident ''MemData''))))]) in
guard g s"

definition n_RecvGntS::"nat \<Rightarrow> rule" where [simp]:
"n_RecvGntS  i\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntS)) in
let s = (parallelList [(assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const S))), (assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty))), (assign ((Field (Para (Ident ''Cache'') i) ''Data''), (IVar (Field (Para (Ident ''Chan2'') i) ''Data''))))]) in
guard g s"

definition n_RecvGntE::"nat \<Rightarrow> rule" where [simp]:
"n_RecvGntE  i\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntE)) in
let s = (parallelList [(assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const E))), (assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty))), (assign ((Field (Para (Ident ''Cache'') i) ''Data''), (IVar (Field (Para (Ident ''Chan2'') i) ''Data''))))]) in
guard g s"

definition n_Store::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_Store  i d\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) in
let s = (parallelList [(assign ((Field (Para (Ident ''Cache'') i) ''Data''), (Const (index d)))), (assign ((Ident ''AuxData''), (Const (index d))))]) in
guard g s"

subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> j. j\<le>N\<and>r=n_SendReqS  j) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqEI  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqES  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvReq N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInvE  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInvS  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInvAck  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvInvAck  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendGntS  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendGntE N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvGntS  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvGntE  i) \<or>
(\<exists> i d. i\<le>N\<and>d\<le>N\<and>r=n_Store  i d)
}"



subsection{*Definitions of a Formally Parameterized Invariant Formulas*}

definition inv__1::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__1 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E)) (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv3) ''State'')) (Const E))))"

definition inv__2::"formula" where [simp]:
"inv__2  \<equiv>
(neg (andForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (neg (eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData''))))))"

definition inv__3::"nat \<Rightarrow> formula" where [simp]:
"inv__3 p__Inv4 \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const I))) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''Data'')) (IVar (Ident ''AuxData''))))))"

definition inv__4::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__4 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv3) ''Cmd'')) (Const GntE))))"

definition inv__5::"nat \<Rightarrow> formula" where [simp]:
"inv__5 p__Inv4 \<equiv>
(neg (andForm (andForm (neg (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Data'')) (IVar (Ident ''AuxData'')))) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck))))"

definition inv__6::"nat \<Rightarrow> formula" where [simp]:
"inv__6 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E))))"

definition inv__7::"nat \<Rightarrow> formula" where [simp]:
"inv__7 p__Inv4 \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Data'')) (IVar (Ident ''AuxData'')))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntS))))"

definition inv__8::"nat \<Rightarrow> formula" where [simp]:
"inv__8 p__Inv4 \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Data'')) (IVar (Ident ''AuxData'')))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntE))))"

definition inv__9::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__9 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv3) ''State'')) (Const I))) (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E))))"

definition inv__10::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__10 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntE)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv3) ''Cmd'')) (Const GntE))))"

definition inv__11::"nat \<Rightarrow> formula" where [simp]:
"inv__11 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E)))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Inv))))"

definition inv__12::"nat \<Rightarrow> formula" where [simp]:
"inv__12 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck)) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv4)) (Const false))))"

definition inv__13::"nat \<Rightarrow> formula" where [simp]:
"inv__13 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck)) (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E))))"

definition inv__14::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__14 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv3) ''Cmd'')) (Const InvAck)) (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E))))"

definition inv__15::"nat \<Rightarrow> formula" where [simp]:
"inv__15 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntE))))"

definition inv__16::"nat \<Rightarrow> formula" where [simp]:
"inv__16 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntS)) (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E))))"

definition inv__17::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__17 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv3) ''Cmd'')) (Const GntS)) (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E))))"

definition inv__18::"nat \<Rightarrow> formula" where [simp]:
"inv__18 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntE)) (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E))))"

definition inv__19::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__19 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const I))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv3) ''Cmd'')) (Const GntE))))"

definition inv__20::"nat \<Rightarrow> formula" where [simp]:
"inv__20 p__Inv4 \<equiv>
(neg (andForm (andForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E)))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Empty))) (eqn (IVar (Para (Ident ''InvSet'') p__Inv4)) (Const true))))"

definition inv__21::"nat \<Rightarrow> formula" where [simp]:
"inv__21 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Inv)) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv4)) (Const false))))"

definition inv__22::"nat \<Rightarrow> formula" where [simp]:
"inv__22 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntE))))"

definition inv__23::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__23 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv3) ''State'')) (Const E)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Inv))))"

definition inv__24::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__24 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv3) ''Cmd'')) (Const GntE))))"

definition inv__25::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__25 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntS)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv3) ''Cmd'')) (Const GntE))))"

definition inv__26::"nat \<Rightarrow> formula" where [simp]:
"inv__26 p__Inv4 \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const I))) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv4)) (Const false))))"

definition inv__27::"nat \<Rightarrow> formula" where [simp]:
"inv__27 p__Inv4 \<equiv>
(neg (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E)))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Empty))) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv4)) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const Empty))))"

definition inv__28::"nat \<Rightarrow> formula" where [simp]:
"inv__28 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Inv))))"

definition inv__29::"nat \<Rightarrow> formula" where [simp]:
"inv__29 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv4)) (Const false))))"

definition inv__30::"nat \<Rightarrow> formula" where [simp]:
"inv__30 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntS))))"

definition inv__31::"nat \<Rightarrow> formula" where [simp]:
"inv__31 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Inv)) (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck))))"

definition inv__32::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__32 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const E)) (eqn (IVar (Para (Ident ''InvSet'') p__Inv3)) (Const true))))"

definition inv__33::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__33 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv3) ''Cmd'')) (Const Inv)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntE))))"

definition inv__34::"nat \<Rightarrow> formula" where [simp]:
"inv__34 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntS)) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv4)) (Const false))))"

definition inv__35::"nat \<Rightarrow> formula" where [simp]:
"inv__35 p__Inv4 \<equiv>
(neg (andForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const I))) (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck))))"

definition inv__36::"nat \<Rightarrow> formula" where [simp]:
"inv__36 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv4)) (Const false)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntE))))"

definition inv__37::"nat \<Rightarrow> formula" where [simp]:
"inv__37 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Inv))))"

definition inv__38::"nat \<Rightarrow> formula" where [simp]:
"inv__38 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck))))"

definition inv__39::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__39 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv3) ''State'')) (Const E)) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv4)) (Const true))))"

definition inv__40::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__40 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv3) ''Cmd'')) (Const GntE))))"

definition inv__41::"nat \<Rightarrow> formula" where [simp]:
"inv__41 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntS)) (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck))))"

definition inv__42::"nat \<Rightarrow> formula" where [simp]:
"inv__42 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Inv)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (eqn (IVar (Ident ''ExGntd'')) (Const false))))"

definition inv__43::"nat \<Rightarrow> formula" where [simp]:
"inv__43 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''CurCmd'')) (Const Empty))))"

definition inv__44::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__44 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv3)) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntE))))"

definition inv__45::"nat \<Rightarrow> formula" where [simp]:
"inv__45 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (eqn (IVar (Ident ''ExGntd'')) (Const false))))"

definition inv__46::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__46 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv3) ''Cmd'')) (Const Inv)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck))))"

definition inv__47::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__47 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv3) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv4) ''Cmd'')) (Const InvAck))))"

definition inv__48::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__48 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) (eqn (IVar (Field (Para (Ident ''Chan3'') p__Inv3) ''Cmd'')) (Const InvAck))) (eqn (IVar (Para (Ident ''InvSet'') p__Inv4)) (Const true))))"

definition inv__49::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__49 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Inv)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv3) ''Cmd'')) (Const Inv))))"

definition inv__50::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__50 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) (eqn (IVar (Para (Ident ''InvSet'') p__Inv3)) (Const true))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const Inv))))"

definition inv__51::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__51 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Ident ''InvSet'') p__Inv4)) (Const true)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (eqn (IVar (Para (Ident ''InvSet'') p__Inv3)) (Const true))))"

definition inv__52::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__52 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (andForm (eqn (IVar (Para (Ident ''ShrSet'') p__Inv3)) (Const true)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv4)) (Const true))))"

subsection{*Definitions of  the Set of Invariant Formula Instances in a $N$-protocol Instance*}
definition invariants::"nat \<Rightarrow> formula set" where [simp]:
"invariants N \<equiv> {f.
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4) \<or>
(f=inv__2  ) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__4  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__5  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__6  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__7  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__8  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__9  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__10  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__11  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__12  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__13  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__14  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__15  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__16  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__17  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__18  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__19  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__20  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__21  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__22  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__23  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__24  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__25  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__26  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__27  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__28  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__29  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__30  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__31  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__32  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__33  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__34  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__35  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__36  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__37  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__38  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__39  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__40  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__41  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__42  p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__43  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__44  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__45  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__46  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__47  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__48  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__49  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__50  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__51  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__52  p__Inv3 p__Inv4)
}"



subsection{*Definitions of initial states*}

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty))))"

definition initSpec1::"nat \<Rightarrow> formula" where [simp]:
"initSpec1 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty))))"

definition initSpec2::"nat \<Rightarrow> formula" where [simp]:
"initSpec2 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))))"

definition initSpec3::"nat \<Rightarrow> formula" where [simp]:
"initSpec3 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Data'')) (Const (index 1)))))"

definition initSpec4::"nat \<Rightarrow> formula" where [simp]:
"initSpec4 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Data'')) (Const (index 1)))))"

definition initSpec5::"nat \<Rightarrow> formula" where [simp]:
"initSpec5 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Data'')) (Const (index 1)))))"

definition initSpec6::"nat \<Rightarrow> formula" where [simp]:
"initSpec6 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))))"

definition initSpec7::"nat \<Rightarrow> formula" where [simp]:
"initSpec7 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Cache'') i) ''Data'')) (Const (index 1)))))"

definition initSpec8::"nat \<Rightarrow> formula" where [simp]:
"initSpec8 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''ShrSet'') i)) (Const false))))"

definition initSpec9::"nat \<Rightarrow> formula" where [simp]:
"initSpec9 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''InvSet'') i)) (Const false))))"

definition initSpec10::"formula" where [simp]:
"initSpec10  \<equiv> (eqn (IVar (Ident ''CurCmd'')) (Const Empty))"

definition initSpec11::"formula" where [simp]:
"initSpec11  \<equiv> (eqn (IVar (Ident ''ExGntd'')) (Const false))"

definition initSpec12::"formula" where [simp]:
"initSpec12  \<equiv> (eqn (IVar (Ident ''MemData'')) (Const (index 1)))"

definition initSpec13::"formula" where [simp]:
"initSpec13  \<equiv> (eqn (IVar (Ident ''AuxData'')) (Const (index 1)))"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 N),
(initSpec2 N),
(initSpec3 N),
(initSpec4 N),
(initSpec5 N),
(initSpec6 N),
(initSpec7 N),
(initSpec8 N),
(initSpec9 N),
(initSpec10 ),
(initSpec11 ),
(initSpec12 ),
(initSpec13 )
]"

end
