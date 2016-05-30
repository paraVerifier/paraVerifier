(*  Title:      HOL/Auth/n_german_lemma_on_inv__3.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_german Protocol Case Study*} 

theory n_german_lemma_on_inv__3 imports n_german_base
begin
section{*All lemmas on causal relation between inv__3 and some rule r*}
lemma n_SendInvAckVsinv__3:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_SendInvAck  i)" and
a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_SendInvAck  i" apply fastforce done
from a2 obtain p__Inv4 where a2:"p__Inv4\<le>N\<and>f=inv__3  p__Inv4" apply fastforce done
have "(i=p__Inv4)\<or>(i~=p__Inv4)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv4)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv4)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_RecvGntSVsinv__3:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_RecvGntS  i)" and
a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_RecvGntS  i" apply fastforce done
from a2 obtain p__Inv4 where a2:"p__Inv4\<le>N\<and>f=inv__3  p__Inv4" apply fastforce done
have "(i=p__Inv4)\<or>(i~=p__Inv4)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv4)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Data'')) (IVar (Ident ''AuxData'')))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntS))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv4)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_RecvGntEVsinv__3:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_RecvGntE  i)" and
a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_RecvGntE  i" apply fastforce done
from a2 obtain p__Inv4 where a2:"p__Inv4\<le>N\<and>f=inv__3  p__Inv4" apply fastforce done
have "(i=p__Inv4)\<or>(i~=p__Inv4)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv4)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (neg (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Data'')) (IVar (Ident ''AuxData'')))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv4) ''Cmd'')) (Const GntE))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv4)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_StoreVsinv__3:
assumes a1: "(\<exists> i d. i\<le>N\<and>d\<le>N\<and>r=n_Store  i d)" and
a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i d where a1:"i\<le>N\<and>d\<le>N\<and>r=n_Store  i d" apply fastforce done
from a2 obtain p__Inv4 where a2:"p__Inv4\<le>N\<and>f=inv__3  p__Inv4" apply fastforce done
have "(i=p__Inv4)\<or>(i~=p__Inv4)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv4)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv4)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv4) ''State'')) (Const I))) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_SendReqESVsinv__3:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_SendReqES  i" and
  a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_RecvInvAckVsinv__3:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_RecvInvAck  i" and
  a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_SendGntSVsinv__3:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_SendGntS  i" and
  a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_SendInvSVsinv__3:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_SendInvS  i" and
  a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_SendInvEVsinv__3:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_SendInvE  i" and
  a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_RecvReqVsinv__3:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_RecvReq N i" and
  a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_SendReqSVsinv__3:
  assumes a1: "\<exists> j. j\<le>N\<and>r=n_SendReqS  j" and
  a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_SendGntEVsinv__3:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_SendGntE N i" and
  a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_SendReqEIVsinv__3:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_SendReqEI  i" and
  a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  
end
