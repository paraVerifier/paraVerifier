(*  Title:      HOL/Auth/n_german_on_inis.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_german Protocol Case Study*} 

theory n_german_on_inis imports n_german_on_ini
begin
lemma on_inis:
  assumes b1: "f \<in> (invariants N)" and b2: "ini \<in> {andList (allInitSpecs N)}" and b3: "formEval ini s"
  shows "formEval f s"
  proof -
  have c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)\<or>
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
  apply (cut_tac b1, simp) done
    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__1)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__2  )"
      have "formEval f s"
      apply (rule iniImply_inv__2)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__3)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__4  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__4)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__5  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__5)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__6  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__6)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__7  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__7)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__8  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__8)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__9  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__9)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__10  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__10)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__11  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__11)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__12  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__12)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__13  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__13)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__14  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__14)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__15  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__15)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__16  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__16)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__17  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__17)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__18  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__18)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__19  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__19)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__20  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__20)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__21  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__21)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__22  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__22)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__23  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__23)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__24  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__24)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__25  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__25)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__26  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__26)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__27  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__27)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__28  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__28)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__29  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__29)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__30  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__30)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__31  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__31)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__32  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__32)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__33  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__33)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__34  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__34)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__35  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__35)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__36  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__36)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__37  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__37)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__38  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__38)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__39  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__39)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__40  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__40)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__41  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__41)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__42  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__42)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__43  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__43)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__44  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__44)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__45  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__45)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__46  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__46)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__47  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__47)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__48  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__48)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__49  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__49)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__50  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__50)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__51  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__51)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__52  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__52)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

  ultimately show "formEval f s"
  by satx
qed

end
