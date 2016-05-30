(*  Title:      HOL/Auth/n_mesi_lemma_inv__2_on_rules.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_mesi Protocol Case Study*} 

theory n_mesi_lemma_inv__2_on_rules imports n_mesi_lemma_on_inv__2
begin
section{*All lemmas on causal relation between inv__2*}
lemma lemma_inv__2_on_rules:
  assumes b1: "r \<in> rules N" and b2: "(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__2  p__Inv0 p__Inv2)"
  shows "invHoldForRule s f r (invariants N)"
  proof -
  have c1: "(\<exists> i. i\<le>N\<and>r=n_t1  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_t2 N i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_t3 N i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_t4 N i)"
  apply (cut_tac b1, auto) done
    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_t1  i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_t1Vsinv__2) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_t2 N i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_t2Vsinv__2) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_t3 N i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_t3Vsinv__2) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_t4 N i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_t4Vsinv__2) done
    }

  ultimately show "invHoldForRule s f r (invariants N)"
  by satx
qed

end
