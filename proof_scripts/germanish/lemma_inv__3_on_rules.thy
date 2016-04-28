theory lemma_inv__3_on_rules imports lemma_on_inv__3
begin
lemma lemma_inv__3_on_rules:
  assumes b1: "r \<in> rules N" and b2: "(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__3  p__Inv0 p__Inv1)"
  shows "invHoldForRule' s f r (invariants N)"
  proof -
  have c1: "(\<exists> i. i\<le>N\<and>r=n_t1  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_t2  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_t3  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_t4  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_t5  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_t6 N i)"
  apply (cut_tac b1, auto) done
    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_t1  i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_t1Vsinv__3) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_t2  i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_t2Vsinv__3) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_t3  i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_t3Vsinv__3) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_t4  i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_t4Vsinv__3) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_t5  i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_t5Vsinv__3) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_t6 N i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_t6Vsinv__3) done
    }

  ultimately show "invHoldForRule' s f r (invariants N)"
  by satx
qed

end
