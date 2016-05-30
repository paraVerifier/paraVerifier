(*  Title:      HOL/Auth/n_germanish_lemma_on_inv__2.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_germanish Protocol Case Study*} 

theory n_germanish_lemma_on_inv__2 imports n_germanish_base
begin
section{*All lemmas on causal relation between inv__2 and some rule r*}
lemma n_t3Vsinv__2:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_t3  i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__2  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_t3  i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__2  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (eqn (IVar (Para (Ident ''cache'') p__Inv2)) (Const exclusive)) (eqn (IVar (Para (Ident ''home_sharer_list'') i)) (Const true))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_t4Vsinv__2:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_t4  i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__2  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_t4  i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__2  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (eqn (IVar (Para (Ident ''cache'') p__Inv2)) (Const exclusive)) (eqn (IVar (Para (Ident ''home_sharer_list'') i)) (Const true))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_t5Vsinv__2:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_t5  i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__2  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_t5  i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__2  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_t6Vsinv__2:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_t6 N i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__2  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_t6 N i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__2  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_t2Vsinv__2:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_t2  i" and
  a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__2  p__Inv2)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_t1Vsinv__2:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_t1  i" and
  a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__2  p__Inv2)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  
end
