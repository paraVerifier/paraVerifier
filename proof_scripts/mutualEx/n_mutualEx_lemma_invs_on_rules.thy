(*  Title:      HOL/Auth/n_mutualEx_lemma_invs_on_rules.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_mutualEx Protocol Case Study*} 

theory n_mutualEx_lemma_invs_on_rules imports n_mutualEx_lemma_inv__1_on_rules n_mutualEx_lemma_inv__2_on_rules n_mutualEx_lemma_inv__3_on_rules n_mutualEx_lemma_inv__4_on_rules n_mutualEx_lemma_inv__5_on_rules
begin
lemma invs_on_rules:
  assumes a1: "f \<in> invariants N" and a2: "r \<in> rules N"
  shows "invHoldForRule s f r (invariants N)"
  proof -
  have b1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__2  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__3  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__4  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__5  p__Inv3 p__Inv4)"
  apply (cut_tac a1, auto) done
    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__1_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__2  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__2_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__3  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__3_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__4  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__4_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__5  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__5_on_rules) done
    }

  ultimately show "invHoldForRule s f r (invariants N)"
  by satx
qed

end
