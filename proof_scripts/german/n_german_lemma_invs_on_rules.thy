(*  Title:      HOL/Auth/n_german_lemma_invs_on_rules.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_german Protocol Case Study*} 

theory n_german_lemma_invs_on_rules imports n_german_lemma_inv__1_on_rules n_german_lemma_inv__2_on_rules n_german_lemma_inv__3_on_rules n_german_lemma_inv__4_on_rules n_german_lemma_inv__5_on_rules n_german_lemma_inv__6_on_rules n_german_lemma_inv__7_on_rules n_german_lemma_inv__8_on_rules n_german_lemma_inv__9_on_rules n_german_lemma_inv__10_on_rules n_german_lemma_inv__11_on_rules n_german_lemma_inv__12_on_rules n_german_lemma_inv__13_on_rules n_german_lemma_inv__14_on_rules n_german_lemma_inv__15_on_rules n_german_lemma_inv__16_on_rules n_german_lemma_inv__17_on_rules n_german_lemma_inv__18_on_rules n_german_lemma_inv__19_on_rules n_german_lemma_inv__20_on_rules n_german_lemma_inv__21_on_rules n_german_lemma_inv__22_on_rules n_german_lemma_inv__23_on_rules n_german_lemma_inv__24_on_rules n_german_lemma_inv__25_on_rules n_german_lemma_inv__26_on_rules n_german_lemma_inv__27_on_rules n_german_lemma_inv__28_on_rules n_german_lemma_inv__29_on_rules n_german_lemma_inv__30_on_rules n_german_lemma_inv__31_on_rules n_german_lemma_inv__32_on_rules n_german_lemma_inv__33_on_rules n_german_lemma_inv__34_on_rules n_german_lemma_inv__35_on_rules n_german_lemma_inv__36_on_rules n_german_lemma_inv__37_on_rules n_german_lemma_inv__38_on_rules n_german_lemma_inv__39_on_rules n_german_lemma_inv__40_on_rules n_german_lemma_inv__41_on_rules n_german_lemma_inv__42_on_rules n_german_lemma_inv__43_on_rules n_german_lemma_inv__44_on_rules n_german_lemma_inv__45_on_rules n_german_lemma_inv__46_on_rules n_german_lemma_inv__47_on_rules n_german_lemma_inv__48_on_rules n_german_lemma_inv__49_on_rules n_german_lemma_inv__50_on_rules n_german_lemma_inv__51_on_rules n_german_lemma_inv__52_on_rules
begin
lemma invs_on_rules:
  assumes a1: "f \<in> invariants N" and a2: "r \<in> rules N"
  shows "invHoldForRule s f r (invariants N)"
  proof -
  have b1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)\<or>
    (f=inv__2  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__4  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__5  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__6  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__7  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__8  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__9  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__10  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__11  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__12  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__13  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__14  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__15  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__16  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__17  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__18  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__19  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__20  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__21  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__22  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__23  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__24  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__25  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__26  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__27  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__28  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__29  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__30  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__31  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__32  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__33  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__34  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__35  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__36  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__37  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__38  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__39  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__40  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__41  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__42  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__43  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__44  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__45  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__46  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__47  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__48  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__49  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__50  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__51  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__52  p__Inv3 p__Inv4)"
  apply (cut_tac a1, auto) done
    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__1_on_rules) done
    }

    moreover {
      assume c1: "(f=inv__2  )"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__2_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__3_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__4  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__4_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__5  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__5_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__6  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__6_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__7  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__7_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__8  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__8_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__9  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__9_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__10  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__10_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__11  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__11_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__12  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__12_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__13  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__13_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__14  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__14_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__15  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__15_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__16  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__16_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__17  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__17_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__18  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__18_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__19  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__19_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__20  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__20_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__21  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__21_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__22  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__22_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__23  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__23_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__24  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__24_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__25  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__25_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__26  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__26_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__27  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__27_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__28  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__28_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__29  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__29_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__30  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__30_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__31  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__31_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__32  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__32_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__33  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__33_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__34  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__34_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__35  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__35_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__36  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__36_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__37  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__37_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__38  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__38_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__39  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__39_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__40  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__40_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__41  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__41_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__42  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__42_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__43  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__43_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__44  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__44_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__45  p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__45_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__46  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__46_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__47  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__47_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__48  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__48_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__49  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__49_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__50  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__50_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__51  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__51_on_rules) done
    }

    moreover {
      assume c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__52  p__Inv3 p__Inv4)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac a2 c1, metis lemma_inv__52_on_rules) done
    }

  ultimately show "invHoldForRule s f r (invariants N)"
  by satx
qed

end
