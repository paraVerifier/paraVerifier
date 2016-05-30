(*  Title:      HOL/Auth/n_german_lemma_inv__38_on_rules.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_german Protocol Case Study*} 

theory n_german_lemma_inv__38_on_rules imports n_german_lemma_on_inv__38
begin
section{*All lemmas on causal relation between inv__38*}
lemma lemma_inv__38_on_rules:
  assumes b1: "r \<in> rules N" and b2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__38  p__Inv4)"
  shows "invHoldForRule s f r (invariants N)"
  proof -
  have c1: "(\<exists> j. j\<le>N\<and>r=n_SendReqS  j)\<or>
    (\<exists> i. i\<le>N\<and>r=n_SendReqEI  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_SendReqES  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_RecvReq N i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_SendInvE  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_SendInvS  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_SendInvAck  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_RecvInvAck  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_SendGntS  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_SendGntE N i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_RecvGntS  i)\<or>
    (\<exists> i. i\<le>N\<and>r=n_RecvGntE  i)\<or>
    (\<exists> i d. i\<le>N\<and>d\<le>N\<and>r=n_Store  i d)"
  apply (cut_tac b1, auto) done
    moreover {
      assume d1: "(\<exists> j. j\<le>N\<and>r=n_SendReqS  j)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_SendReqSVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_SendReqEI  i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_SendReqEIVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_SendReqES  i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_SendReqESVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_RecvReq N i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_RecvReqVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_SendInvE  i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_SendInvEVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_SendInvS  i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_SendInvSVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_SendInvAck  i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_SendInvAckVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_RecvInvAck  i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_RecvInvAckVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_SendGntS  i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_SendGntSVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_SendGntE N i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_SendGntEVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_RecvGntS  i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_RecvGntSVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i. i\<le>N\<and>r=n_RecvGntE  i)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_RecvGntEVsinv__38) done
    }

    moreover {
      assume d1: "(\<exists> i d. i\<le>N\<and>d\<le>N\<and>r=n_Store  i d)"
      have "invHoldForRule s f r (invariants N)"
      apply (cut_tac b2 d1, metis n_StoreVsinv__38) done
    }

  ultimately show "invHoldForRule s f r (invariants N)"
  by satx
qed

end
