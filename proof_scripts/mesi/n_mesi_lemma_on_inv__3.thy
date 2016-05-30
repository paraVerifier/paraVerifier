(*  Title:      HOL/Auth/n_mesi_lemma_on_inv__3.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_mesi Protocol Case Study*} 

theory n_mesi_lemma_on_inv__3 imports n_mesi_base
begin
section{*All lemmas on causal relation between inv__3 and some rule r*}
lemma n_t1Vsinv__3:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_t1  i)" and
a2: "(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_t1  i" apply fastforce done
from a2 obtain p__Inv0 p__Inv2 where a2:"p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i=p__Inv0)\<or>(i~=p__Inv0\<and>i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv0)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv0\<and>i~=p__Inv2)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_t2Vsinv__3:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_t2 N i)" and
a2: "(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_t2 N i" apply fastforce done
from a2 obtain p__Inv0 p__Inv2 where a2:"p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i=p__Inv0)\<or>(i~=p__Inv0\<and>i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "((formEval (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)) s))\<or>((formEval (andForm (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))" by auto
  moreover {
    assume c1: "((formEval (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  ultimately have "invHoldForRule s f r (invariants N)" by satx
}
moreover {
  assume b1: "(i=p__Inv0)"
  have "((formEval (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)) s))\<or>((formEval (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) s))\<or>((formEval (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) s))\<or>((formEval (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) s))" by auto
  moreover {
    assume c1: "((formEval (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  ultimately have "invHoldForRule s f r (invariants N)" by satx
}
moreover {
  assume b1: "(i~=p__Inv0\<and>i~=p__Inv2)"
  have "((formEval (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E))) s))\<or>((formEval (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E))) s))\<or>((formEval (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E))) s))\<or>((formEval (andForm (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E))) s))\<or>((formEval (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))\<or>((formEval (andForm (andForm (andForm (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))" by auto
  moreover {
    assume c1: "((formEval (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I)) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (andForm (andForm (andForm (andForm (andForm (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const I))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv2)) (Const E)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const I)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const M)))) (neg (eqn (IVar (Para (Ident ''state'') p__Inv0)) (Const E)))) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  ultimately have "invHoldForRule s f r (invariants N)" by satx
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_t3Vsinv__3:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_t3 N i)" and
a2: "(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_t3 N i" apply fastforce done
from a2 obtain p__Inv0 p__Inv2 where a2:"p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i=p__Inv0)\<or>(i~=p__Inv0\<and>i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv0)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv0\<and>i~=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_t4Vsinv__3:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_t4 N i)" and
a2: "(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_t4 N i" apply fastforce done
from a2 obtain p__Inv0 p__Inv2 where a2:"p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i=p__Inv0)\<or>(i~=p__Inv0\<and>i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv0)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv0\<and>i~=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed
end
