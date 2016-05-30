(*  Title:      HOL/Auth/n_moesi_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_moesi Protocol Case Study*} 

theory n_moesi_base imports paraTheory
begin

section{*Main definitions*}

subsection{* Definitions of Constants*}
definition M::"scalrValueType" where [simp]: "M\<equiv> enum ''control'' ''M''"
definition OSTATUS::"scalrValueType" where [simp]: "OSTATUS\<equiv> enum ''control'' ''OSTATUS''"
definition E::"scalrValueType" where [simp]: "E\<equiv> enum ''control'' ''E''"
definition S::"scalrValueType" where [simp]: "S\<equiv> enum ''control'' ''S''"
definition I::"scalrValueType" where [simp]: "I\<equiv> enum ''control'' ''I''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"



subsection{*  Definitions of Parameterized Rules *}

definition n_rule_t1::"nat \<Rightarrow> rule" where [simp]:
"n_rule_t1  i\<equiv>
let g = (eqn (IVar (Para (Ident ''a'') i)) (Const E)) in
let s = (parallelList [(assign ((Para (Ident ''a'') i), (Const M)))]) in
guard g s"

definition n_rule_t2::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_rule_t2 N i\<equiv>
let g = (eqn (IVar (Para (Ident ''a'') i)) (Const I)) in
let s = (parallelList [(forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''a'') j), (iteForm (eqn (Const (index j)) (Const (index i))) (Const S) (iteForm (eqn (IVar (Para (Ident ''a'') j)) (Const E)) (Const S) (iteForm (eqn (IVar (Para (Ident ''a'') j)) (Const M)) (Const OSTATUS) (IVar (Para (Ident ''a'') j)))))))))]) in
guard g s"

definition n_rul_t3::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_rul_t3 N i\<equiv>
let g = (eqn (IVar (Para (Ident ''a'') i)) (Const S)) in
let s = (parallelList [(forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''a'') j), (iteForm (eqn (Const (index j)) (Const (index i))) (Const E) (Const I))))))]) in
guard g s"

definition n_rul_t4::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_rul_t4 N i\<equiv>
let g = (eqn (IVar (Para (Ident ''a'') i)) (Const OSTATUS)) in
let s = (parallelList [(forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''a'') j), (iteForm (eqn (Const (index j)) (Const (index i))) (Const E) (Const I))))))]) in
guard g s"

definition n_rul_t5::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_rul_t5 N i\<equiv>
let g = (eqn (IVar (Para (Ident ''a'') i)) (Const I)) in
let s = (parallelList [(forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''a'') j), (iteForm (eqn (Const (index j)) (Const (index i))) (Const E) (Const I))))))]) in
guard g s"

subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_rule_t1  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_rule_t2 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_rul_t3 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_rul_t4 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_rul_t5 N i)
}"



subsection{*Definitions of a Formally Parameterized Invariant Formulas*}

definition inv__1::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__1 p__Inv0 p__Inv2 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''a'') p__Inv2)) (Const M)) (eqn (IVar (Para (Ident ''a'') p__Inv0)) (Const M))))"

definition inv__2::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__2 p__Inv0 p__Inv2 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''a'') p__Inv2)) (Const M)) (eqn (IVar (Para (Ident ''a'') p__Inv0)) (Const E))))"

definition inv__3::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__3 p__Inv0 p__Inv2 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''a'') p__Inv2)) (Const E)) (eqn (IVar (Para (Ident ''a'') p__Inv0)) (Const E))))"

subsection{*Definitions of  the Set of Invariant Formula Instances in a $N$-protocol Instance*}
definition invariants::"nat \<Rightarrow> formula set" where [simp]:
"invariants N \<equiv> {f.
(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__1  p__Inv0 p__Inv2) \<or>
(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__2  p__Inv0 p__Inv2) \<or>
(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2)
}"



subsection{*Definitions of initial states*}

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''a'') i)) (Const I))))"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N)
]"

end
