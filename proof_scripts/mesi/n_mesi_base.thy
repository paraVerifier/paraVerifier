theory n_mesi_base imports paraTheory
begin
section{*Main definitions*}
definition M::"scalrValueType" where [simp]: "M\<equiv> enum ''control'' ''M''"
definition E::"scalrValueType" where [simp]: "E\<equiv> enum ''control'' ''E''"
definition S::"scalrValueType" where [simp]: "S\<equiv> enum ''control'' ''S''"
definition I::"scalrValueType" where [simp]: "I\<equiv> enum ''control'' ''I''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"

definition n_t1::"nat \<Rightarrow> rule" where [simp]:
"n_t1  i\<equiv>
let g = (eqn (IVar (Para (Ident ''state'') i)) (Const E)) in
let s = (parallelList [(assign ((Para (Ident ''state'') i), (Const M)))]) in
guard g s"

definition n_t2::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_t2 N i\<equiv>
let g = (eqn (IVar (Para (Ident ''state'') i)) (Const I)) in
let s = (parallelList [(forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''state'') j), (iteForm (eqn (Const (index j)) (Const (index i))) (Const S) (iteForm (eqn (IVar (Para (Ident ''state'') j)) (Const E)) (Const S) (iteForm (eqn (IVar (Para (Ident ''state'') j)) (Const M)) (Const S) (iteForm (eqn (IVar (Para (Ident ''state'') j)) (Const I)) (Const I) (Const S)))))))))]) in
guard g s"

definition n_t3::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_t3 N i\<equiv>
let g = (eqn (IVar (Para (Ident ''state'') i)) (Const S)) in
let s = (parallelList [(forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''state'') j), (iteForm (eqn (Const (index j)) (Const (index i))) (Const E) (Const I))))))]) in
guard g s"

definition n_t4::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_t4 N i\<equiv>
let g = (eqn (IVar (Para (Ident ''state'') i)) (Const I)) in
let s = (parallelList [(forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''state'') j), (iteForm (eqn (Const (index j)) (Const (index i))) (Const E) (Const I))))))]) in
guard g s"

definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_t1  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_t2 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_t3 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_t4 N i)
}"

definition inv__1::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__1 p__Inv0 p__Inv1 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''state'') p__Inv1)) (Const M)) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M))))"

definition inv__2::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__2 p__Inv0 p__Inv1 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''state'') p__Inv1)) (Const M)) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E))))"

definition inv__3::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__3 p__Inv0 p__Inv1 \<equiv>
(neg (andForm (eqn (IVar (Para (Ident ''state'') p__Inv1)) (Const E)) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E))))"

definition invariants::"nat \<Rightarrow> formula set" where [simp]:
"invariants N \<equiv> {f.
(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__1  p__Inv0 p__Inv1) \<or>
(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__2  p__Inv0 p__Inv1) \<or>
(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__3  p__Inv0 p__Inv1)
}"

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''state'') i)) (Const I))))"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N)
]"

end
