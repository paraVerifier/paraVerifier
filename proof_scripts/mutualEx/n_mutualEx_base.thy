(*  Title:      HOL/Auth/n_mutualEx_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_mutualEx Protocol Case Study*} 

theory n_mutualEx_base imports paraTheory
begin

section{*Main definitions*}

subsection{* Definitions of Constants*}
definition I::"scalrValueType" where [simp]: "I\<equiv> enum ''control'' ''I''"
definition T::"scalrValueType" where [simp]: "T\<equiv> enum ''control'' ''T''"
definition C::"scalrValueType" where [simp]: "C\<equiv> enum ''control'' ''C''"
definition E::"scalrValueType" where [simp]: "E\<equiv> enum ''control'' ''E''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"



subsection{*  Definitions of Parameterized Rules *}

definition n_Try::"nat \<Rightarrow> rule" where [simp]:
"n_Try  i\<equiv>
let g = (eqn (IVar (Para (Ident ''n'') i)) (Const I)) in
let s = (parallelList [(assign ((Para (Ident ''n'') i), (Const T)))]) in
guard g s"

definition n_Crit::"nat \<Rightarrow> rule" where [simp]:
"n_Crit  i\<equiv>
let g = (andForm (eqn (IVar (Para (Ident ''n'') i)) (Const T)) (eqn (IVar (Ident ''x'')) (Const true))) in
let s = (parallelList [(assign ((Para (Ident ''n'') i), (Const C))), (assign ((Ident ''x''), (Const false)))]) in
guard g s"

definition n_Exit::"nat \<Rightarrow> rule" where [simp]:
"n_Exit  i\<equiv>
let g = (eqn (IVar (Para (Ident ''n'') i)) (Const C)) in
let s = (parallelList [(assign ((Para (Ident ''n'') i), (Const E)))]) in
guard g s"

definition n_Idle::"nat \<Rightarrow> rule" where [simp]:
"n_Idle  i\<equiv>
let g = (eqn (IVar (Para (Ident ''n'') i)) (Const E)) in
let s = (parallelList [(assign ((Para (Ident ''n'') i), (Const I))), (assign ((Ident ''x''), (Const true)))]) in
guard g s"

subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_Try  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Crit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Exit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Idle  i)
}"



subsection{*Definitions of a Formally Parameterized Invariant Formulas*}

definition inv__1::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__1 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''n'') p__Inv4)) (Const C)) (eqn (IVar (Para (Ident ''n'') p__Inv3)) (Const C))))"

definition inv__2::"nat \<Rightarrow> formula" where [simp]:
"inv__2 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''n'') p__Inv4)) (Const C)) (eqn (IVar (Ident ''x'')) (Const true))))"

definition inv__3::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__3 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''n'') p__Inv3)) (Const C)) (eqn (IVar (Para (Ident ''n'') p__Inv4)) (Const E))))"

definition inv__4::"nat \<Rightarrow> formula" where [simp]:
"inv__4 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''n'') p__Inv4)) (Const E)) (eqn (IVar (Ident ''x'')) (Const true))))"

definition inv__5::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__5 p__Inv3 p__Inv4 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''n'') p__Inv3)) (Const E)) (eqn (IVar (Para (Ident ''n'') p__Inv4)) (Const E))))"

subsection{*Definitions of  the Set of Invariant Formula Instances in a $N$-protocol Instance*}
definition invariants::"nat \<Rightarrow> formula set" where [simp]:
"invariants N \<equiv> {f.
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__2  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__3  p__Inv3 p__Inv4) \<or>
(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__4  p__Inv4) \<or>
(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__5  p__Inv3 p__Inv4)
}"



subsection{*Definitions of initial states*}

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''n'') i)) (Const I))))"

definition initSpec1::"formula" where [simp]:
"initSpec1  \<equiv> (eqn (IVar (Ident ''x'')) (Const true))"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 )
]"

end
