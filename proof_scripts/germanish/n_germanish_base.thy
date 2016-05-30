(*  Title:      HOL/Auth/n_germanish_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_germanish Protocol Case Study*} 

theory n_germanish_base imports paraTheory
begin

section{*Main definitions*}

subsection{* Definitions of Constants*}
definition epsilon::"scalrValueType" where [simp]: "epsilon\<equiv> enum ''control'' ''epsilon''"
definition req_shared::"scalrValueType" where [simp]: "req_shared\<equiv> enum ''control'' ''req_shared''"
definition req_exclusive::"scalrValueType" where [simp]: "req_exclusive\<equiv> enum ''control'' ''req_exclusive''"
definition invalid::"scalrValueType" where [simp]: "invalid\<equiv> enum ''control'' ''invalid''"
definition shared::"scalrValueType" where [simp]: "shared\<equiv> enum ''control'' ''shared''"
definition exclusive::"scalrValueType" where [simp]: "exclusive\<equiv> enum ''control'' ''exclusive''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"



subsection{*  Definitions of Parameterized Rules *}

definition n_t1::"nat \<Rightarrow> rule" where [simp]:
"n_t1  i\<equiv>
let g = (andForm (eqn (IVar (Para (Ident ''cache'') i)) (Const invalid)) (eqn (IVar (Ident ''home_current_command'')) (Const epsilon))) in
let s = (parallelList [(assign ((Ident ''home_current_command''), (Const req_shared))), (assign ((Ident ''home_current_client''), (Const (index i))))]) in
guard g s"

definition n_t2::"nat \<Rightarrow> rule" where [simp]:
"n_t2  i\<equiv>
let g = (andForm (eqn (IVar (Ident ''home_current_command'')) (Const epsilon)) (neg (eqn (IVar (Para (Ident ''cache'') i)) (Const exclusive)))) in
let s = (parallelList [(assign ((Ident ''home_current_command''), (Const req_exclusive))), (assign ((Ident ''home_current_client''), (Const (index i))))]) in
guard g s"

definition n_t3::"nat \<Rightarrow> rule" where [simp]:
"n_t3  i\<equiv>
let g = (andForm (eqn (IVar (Ident ''home_current_command'')) (Const req_exclusive)) (eqn (IVar (Para (Ident ''home_sharer_list'') i)) (Const true))) in
let s = (parallelList [(assign ((Ident ''home_exclusive_granted''), (Const false))), (assign ((Para (Ident ''cache'') i), (Const invalid))), (assign ((Para (Ident ''home_sharer_list'') i), (Const false)))]) in
guard g s"

definition n_t4::"nat \<Rightarrow> rule" where [simp]:
"n_t4  i\<equiv>
let g = (andForm (andForm (eqn (IVar (Ident ''home_current_command'')) (Const req_shared)) (eqn (IVar (Ident ''home_exclusive_granted'')) (Const true))) (eqn (IVar (Para (Ident ''home_sharer_list'') i)) (Const true))) in
let s = (parallelList [(assign ((Ident ''home_exclusive_granted''), (Const false))), (assign ((Para (Ident ''cache'') i), (Const shared))), (assign ((Para (Ident ''home_sharer_list'') i), (Const true)))]) in
guard g s"

definition n_t5::"nat \<Rightarrow> rule" where [simp]:
"n_t5  i\<equiv>
let g = (andForm (andForm (eqn (IVar (Ident ''home_current_client'')) (Const (index i))) (eqn (IVar (Ident ''home_current_command'')) (Const req_shared))) (eqn (IVar (Ident ''home_exclusive_granted'')) (Const false))) in
let s = (parallelList [(assign ((Ident ''home_current_command''), (Const epsilon))), (assign ((Para (Ident ''home_sharer_list'') i), (Const true))), (assign ((Para (Ident ''cache'') i), (Const shared)))]) in
guard g s"

definition n_t6::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_t6 N i\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Ident ''home_current_client'')) (Const (index i))) (eqn (IVar (Ident ''home_current_command'')) (Const req_exclusive))) (eqn (IVar (Ident ''home_exclusive_granted'')) (Const false))) (forallForm (down N) (\<lambda>c. (eqn (IVar (Para (Ident ''home_sharer_list'') c)) (Const false))))) in
let s = (parallelList [(assign ((Ident ''home_current_command''), (Const epsilon))), (assign ((Ident ''home_exclusive_granted''), (Const true))), (assign ((Para (Ident ''home_sharer_list'') i), (Const true))), (assign ((Para (Ident ''cache'') i), (Const exclusive)))]) in
guard g s"

subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_t1  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_t2  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_t3  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_t4  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_t5  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_t6 N i)
}"



subsection{*Definitions of a Formally Parameterized Invariant Formulas*}

definition inv__1::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__1 p__Inv0 p__Inv2 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''cache'') p__Inv2)) (Const exclusive)) (eqn (IVar (Para (Ident ''cache'') p__Inv0)) (Const exclusive))))"

definition inv__2::"nat \<Rightarrow> formula" where [simp]:
"inv__2 p__Inv2 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''cache'') p__Inv2)) (Const exclusive)) (eqn (IVar (Ident ''home_exclusive_granted'')) (Const false))))"

definition inv__3::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__3 p__Inv0 p__Inv2 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''cache'') p__Inv0)) (Const exclusive)) (eqn (IVar (Para (Ident ''home_sharer_list'') p__Inv2)) (Const true))))"

subsection{*Definitions of  the Set of Invariant Formula Instances in a $N$-protocol Instance*}
definition invariants::"nat \<Rightarrow> formula set" where [simp]:
"invariants N \<equiv> {f.
(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__1  p__Inv0 p__Inv2) \<or>
(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__2  p__Inv2) \<or>
(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2)
}"



subsection{*Definitions of initial states*}

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''cache'') i)) (Const invalid))))"

definition initSpec1::"nat \<Rightarrow> formula" where [simp]:
"initSpec1 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''home_sharer_list'') i)) (Const false))))"

definition initSpec2::"formula" where [simp]:
"initSpec2  \<equiv> (eqn (IVar (Ident ''home_current_client'')) (Const (index 1)))"

definition initSpec3::"formula" where [simp]:
"initSpec3  \<equiv> (eqn (IVar (Ident ''home_current_command'')) (Const epsilon))"

definition initSpec4::"formula" where [simp]:
"initSpec4  \<equiv> (eqn (IVar (Ident ''home_exclusive_granted'')) (Const false))"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 N),
(initSpec2 ),
(initSpec3 ),
(initSpec4 )
]"

end
