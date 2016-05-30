(*  Title:      HOL/Auth/n_flash_on_inis.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_flash Protocol Case Study*} 

theory n_flash_on_inis imports n_flash_on_ini
begin
lemma on_inis:
  assumes b1: "f \<in> (invariants N)" and b2: "ini \<in> {andList (allInitSpecs N)}" and b3: "formEval ini s"
  shows "formEval f s"
  proof -
  have c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__2  p__Inv4)\<or>
    (f=inv__3  )\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__4  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__5  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__6  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__7  p__Inv4)\<or>
    (f=inv__8  )\<or>
    (f=inv__9  )\<or>
    (f=inv__10  )\<or>
    (f=inv__11  )\<or>
    (f=inv__12  )\<or>
    (f=inv__13  )\<or>
    (f=inv__14  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__15  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__16  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__17  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__18  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__19  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__20  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__21  p__Inv4)\<or>
    (f=inv__22  )\<or>
    (f=inv__23  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__24  p__Inv4)\<or>
    (f=inv__25  )\<or>
    (f=inv__26  )\<or>
    (f=inv__27  )\<or>
    (f=inv__28  )\<or>
    (f=inv__29  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__30  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__31  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__32  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__33  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__34  p__Inv4)\<or>
    (f=inv__35  )\<or>
    (f=inv__36  )\<or>
    (f=inv__37  )\<or>
    (f=inv__38  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__39  p__Inv4)\<or>
    (f=inv__40  )\<or>
    (f=inv__41  )\<or>
    (f=inv__42  )\<or>
    (f=inv__43  )\<or>
    (f=inv__44  )\<or>
    (f=inv__45  )\<or>
    (f=inv__46  )\<or>
    (f=inv__47  )\<or>
    (f=inv__48  )\<or>
    (f=inv__49  )\<or>
    (f=inv__50  )\<or>
    (f=inv__51  )\<or>
    (f=inv__52  )\<or>
    (f=inv__53  )\<or>
    (f=inv__54  )\<or>
    (f=inv__55  )\<or>
    (f=inv__56  )\<or>
    (f=inv__57  )\<or>
    (f=inv__58  )\<or>
    (f=inv__59  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__60  p__Inv4)\<or>
    (f=inv__61  )\<or>
    (f=inv__62  )\<or>
    (f=inv__63  )\<or>
    (f=inv__64  )\<or>
    (f=inv__65  )\<or>
    (f=inv__66  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__67  p__Inv4)\<or>
    (f=inv__68  )\<or>
    (f=inv__69  )\<or>
    (f=inv__70  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__71  p__Inv4)\<or>
    (f=inv__72  )\<or>
    (f=inv__73  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__74  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__75  p__Inv4)\<or>
    (f=inv__76  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__77  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__78  p__Inv4)\<or>
    (f=inv__79  )\<or>
    (f=inv__80  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__81  p__Inv4)\<or>
    (f=inv__82  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__83  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__84  p__Inv4)\<or>
    (f=inv__85  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__86  p__Inv4)\<or>
    (f=inv__87  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__88  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__89  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__90  p__Inv4)\<or>
    (f=inv__91  )\<or>
    (f=inv__92  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__93  p__Inv4)\<or>
    (f=inv__94  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__95  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__96  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__97  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__98  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__99  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__100  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__101  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__102  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__103  p__Inv4)\<or>
    (f=inv__104  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__105  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__106  p__Inv4)\<or>
    (f=inv__107  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__108  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__109  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__110  p__Inv4)\<or>
    (f=inv__111  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__112  p__Inv4)\<or>
    (f=inv__113  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__114  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__115  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__116  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__117  p__Inv4)\<or>
    (f=inv__118  )\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__119  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__120  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__121  p__Inv4)\<or>
    (f=inv__122  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__123  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__124  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__125  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__126  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__127  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__128  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__129  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__130  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__131  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__132  p__Inv4)\<or>
    (f=inv__133  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__134  p__Inv4)\<or>
    (f=inv__135  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__136  p__Inv4)\<or>
    (f=inv__137  )\<or>
    (f=inv__138  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__139  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__140  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__141  p__Inv4)\<or>
    (f=inv__142  )\<or>
    (f=inv__143  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__144  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__145  p__Inv4)\<or>
    (f=inv__146  )\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__147  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__148  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__149  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__150  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__151  p__Inv4)\<or>
    (f=inv__152  )\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__153  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__154  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__155  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__156  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__157  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__158  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__159  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__160  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__161  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__162  p__Inv4)"
  apply (cut_tac b1, simp) done
    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__1)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__2  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__2)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__3  )"
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
      assume d1: "(f=inv__8  )"
      have "formEval f s"
      apply (rule iniImply_inv__8)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__9  )"
      have "formEval f s"
      apply (rule iniImply_inv__9)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__10  )"
      have "formEval f s"
      apply (rule iniImply_inv__10)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__11  )"
      have "formEval f s"
      apply (rule iniImply_inv__11)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__12  )"
      have "formEval f s"
      apply (rule iniImply_inv__12)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__13  )"
      have "formEval f s"
      apply (rule iniImply_inv__13)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__14  )"
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
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__16  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__16)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__17  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__19  p__Inv4)"
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
      assume d1: "(f=inv__22  )"
      have "formEval f s"
      apply (rule iniImply_inv__22)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__23  )"
      have "formEval f s"
      apply (rule iniImply_inv__23)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__24  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__24)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__25  )"
      have "formEval f s"
      apply (rule iniImply_inv__25)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__26  )"
      have "formEval f s"
      apply (rule iniImply_inv__26)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__27  )"
      have "formEval f s"
      apply (rule iniImply_inv__27)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__28  )"
      have "formEval f s"
      apply (rule iniImply_inv__28)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__29  )"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__32  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__32)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__33  p__Inv4)"
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
      assume d1: "(f=inv__35  )"
      have "formEval f s"
      apply (rule iniImply_inv__35)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__36  )"
      have "formEval f s"
      apply (rule iniImply_inv__36)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__37  )"
      have "formEval f s"
      apply (rule iniImply_inv__37)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__38  )"
      have "formEval f s"
      apply (rule iniImply_inv__38)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__39  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__39)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__40  )"
      have "formEval f s"
      apply (rule iniImply_inv__40)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__41  )"
      have "formEval f s"
      apply (rule iniImply_inv__41)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__42  )"
      have "formEval f s"
      apply (rule iniImply_inv__42)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__43  )"
      have "formEval f s"
      apply (rule iniImply_inv__43)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__44  )"
      have "formEval f s"
      apply (rule iniImply_inv__44)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__45  )"
      have "formEval f s"
      apply (rule iniImply_inv__45)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__46  )"
      have "formEval f s"
      apply (rule iniImply_inv__46)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__47  )"
      have "formEval f s"
      apply (rule iniImply_inv__47)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__48  )"
      have "formEval f s"
      apply (rule iniImply_inv__48)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__49  )"
      have "formEval f s"
      apply (rule iniImply_inv__49)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__50  )"
      have "formEval f s"
      apply (rule iniImply_inv__50)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__51  )"
      have "formEval f s"
      apply (rule iniImply_inv__51)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__52  )"
      have "formEval f s"
      apply (rule iniImply_inv__52)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__53  )"
      have "formEval f s"
      apply (rule iniImply_inv__53)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__54  )"
      have "formEval f s"
      apply (rule iniImply_inv__54)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__55  )"
      have "formEval f s"
      apply (rule iniImply_inv__55)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__56  )"
      have "formEval f s"
      apply (rule iniImply_inv__56)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__57  )"
      have "formEval f s"
      apply (rule iniImply_inv__57)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__58  )"
      have "formEval f s"
      apply (rule iniImply_inv__58)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__59  )"
      have "formEval f s"
      apply (rule iniImply_inv__59)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__60  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__60)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__61  )"
      have "formEval f s"
      apply (rule iniImply_inv__61)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__62  )"
      have "formEval f s"
      apply (rule iniImply_inv__62)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__63  )"
      have "formEval f s"
      apply (rule iniImply_inv__63)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__64  )"
      have "formEval f s"
      apply (rule iniImply_inv__64)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__65  )"
      have "formEval f s"
      apply (rule iniImply_inv__65)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__66  )"
      have "formEval f s"
      apply (rule iniImply_inv__66)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__67  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__67)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__68  )"
      have "formEval f s"
      apply (rule iniImply_inv__68)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__69  )"
      have "formEval f s"
      apply (rule iniImply_inv__69)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__70  )"
      have "formEval f s"
      apply (rule iniImply_inv__70)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__71  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__71)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__72  )"
      have "formEval f s"
      apply (rule iniImply_inv__72)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__73  )"
      have "formEval f s"
      apply (rule iniImply_inv__73)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__74  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__74)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__75  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__75)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__76  )"
      have "formEval f s"
      apply (rule iniImply_inv__76)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__77  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__77)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__78  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__78)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__79  )"
      have "formEval f s"
      apply (rule iniImply_inv__79)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__80  )"
      have "formEval f s"
      apply (rule iniImply_inv__80)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__81  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__81)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__82  )"
      have "formEval f s"
      apply (rule iniImply_inv__82)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__83  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__83)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__84  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__84)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__85  )"
      have "formEval f s"
      apply (rule iniImply_inv__85)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__86  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__86)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__87  )"
      have "formEval f s"
      apply (rule iniImply_inv__87)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__88  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__88)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__89  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__89)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__90  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__90)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__91  )"
      have "formEval f s"
      apply (rule iniImply_inv__91)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__92  )"
      have "formEval f s"
      apply (rule iniImply_inv__92)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__93  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__93)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__94  )"
      have "formEval f s"
      apply (rule iniImply_inv__94)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__95  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__95)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__96  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__96)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__97  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__97)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__98  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__98)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__99  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__99)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__100  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__100)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__101  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__101)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__102  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__102)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__103  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__103)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__104  )"
      have "formEval f s"
      apply (rule iniImply_inv__104)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__105  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__105)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__106  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__106)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__107  )"
      have "formEval f s"
      apply (rule iniImply_inv__107)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__108  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__108)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__109  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__109)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__110  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__110)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__111  )"
      have "formEval f s"
      apply (rule iniImply_inv__111)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__112  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__112)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__113  )"
      have "formEval f s"
      apply (rule iniImply_inv__113)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__114  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__114)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__115  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__115)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__116  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__116)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__117  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__117)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__118  )"
      have "formEval f s"
      apply (rule iniImply_inv__118)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__119  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__119)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__120  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__120)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__121  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__121)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__122  )"
      have "formEval f s"
      apply (rule iniImply_inv__122)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__123  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__123)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__124  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__124)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__125  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__125)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__126  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__126)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__127  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__127)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__128  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__128)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__129  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__129)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__130  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__130)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__131  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__131)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__132  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__132)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__133  )"
      have "formEval f s"
      apply (rule iniImply_inv__133)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__134  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__134)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__135  )"
      have "formEval f s"
      apply (rule iniImply_inv__135)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__136  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__136)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__137  )"
      have "formEval f s"
      apply (rule iniImply_inv__137)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__138  )"
      have "formEval f s"
      apply (rule iniImply_inv__138)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__139  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__139)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__140  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__140)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__141  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__141)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__142  )"
      have "formEval f s"
      apply (rule iniImply_inv__142)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__143  )"
      have "formEval f s"
      apply (rule iniImply_inv__143)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__144  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__144)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__145  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__145)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__146  )"
      have "formEval f s"
      apply (rule iniImply_inv__146)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__147  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__147)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__148  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__148)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__149  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__149)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__150  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__150)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__151  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__151)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__152  )"
      have "formEval f s"
      apply (rule iniImply_inv__152)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__153  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__153)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__154  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__154)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__155  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__155)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__156  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__156)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__157  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__157)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__158  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__158)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__159  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__159)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__160  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__160)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__161  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__161)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__162  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__162)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

  ultimately show "formEval f s"
  by satx
qed

end
