theory lemma_inv__1_on_rules imports lemma_on_inv__1
begin
lemma lemma_inv__1_on_rules:
  assumes b1: "r \<in> rules N" and b2: "(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__1  p__Inv0 p__Inv1)"
  shows "invHoldForRule' s f r (invariants N)"
  proof -
  have c1: "(\<exists> i. i\<le>N\<and>r=n_rule_t1  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_rule_t2 N i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_rul_t3 N i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_rul_t4 N i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_rul_t5 N i)"
  apply (cut_tac b1, auto) done
    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_rule_t1  i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_rule_t1Vsinv__1) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_rule_t2 N i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_rule_t2Vsinv__1) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_rul_t3 N i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_rul_t3Vsinv__1) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_rul_t4 N i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_rul_t4Vsinv__1) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_rul_t5 N i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_rul_t5Vsinv__1) done
    }

  ultimately show "invHoldForRule' s f r (invariants N)"
  by satx
qed

end
