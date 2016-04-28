theory lemma_inv__1_on_rules imports lemma_on_inv__1
begin
lemma lemma_inv__1_on_rules:
  assumes b1: "r \<in> rules N" and b2: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)"
  shows "invHoldForRule' s f r (invariants N)"
  proof -
  have c1: "(\<exists> i. i\<le>N\<and>r=n_Try  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_Crit  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_Exit  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_Idle  i)"
  apply (cut_tac b1, auto) done
    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_Try  i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_TryVsinv__1) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_Crit  i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_CritVsinv__1) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_Exit  i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_ExitVsinv__1) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_Idle  i)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_IdleVsinv__1) done
    }

  ultimately show "invHoldForRule' s f r (invariants N)"
  by satx
qed

end
