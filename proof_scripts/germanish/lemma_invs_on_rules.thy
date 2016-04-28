theory lemma_invs_on_rules imports lemma_inv__1_on_rules lemma_inv__2_on_rules lemma_inv__3_on_rules
begin
lemma invs_on_rules:
  assumes a1: "f \<in> invariants N" and a2: "r \<in> rules N"
  shows "invHoldForRule' s f r (invariants N)"
  proof -
  have b1: "(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__1  p__Inv0 p__Inv1)\<or>
    (\<exists> p__Inv1. p__Inv1\<le>N\<and>f=inv__2  p__Inv1)\<or>
    (\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__3  p__Inv0 p__Inv1)"
  apply (cut_tac a1, auto) done
    moreover {
      assume c1: "(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__1  p__Inv0 p__Inv1)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__1_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv1. p__Inv1\<le>N\<and>f=inv__2  p__Inv1)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__2_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__3  p__Inv0 p__Inv1)"
      have "invHoldForRule' s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__3_on_rules) done
    }

  ultimately show "invHoldForRule' s f r (invariants N)"
  by satx
qed

end
