(*  Title:      HOL/Auth/n_flash_nodata_cub_on_inis.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_flash_nodata_cub Protocol Case Study*} 

theory n_flash_nodata_cub_on_inis imports n_flash_nodata_cub_on_ini
begin
lemma on_inis:
  assumes b1: "f \<in> (invariants N)" and b2: "ini \<in> {andList (allInitSpecs N)}" and b3: "formEval ini s"
  shows "formEval f s"
  proof -
  have c1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__2  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__3  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__4  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__5  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__6  p__Inv4)\<or>
    (f=inv__7  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__8  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__9  p__Inv3 p__Inv4)\<or>
    (f=inv__10  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__11  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__12  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__13  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__14  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__15  p__Inv4)\<or>
    (f=inv__16  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__17  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__18  p__Inv4)\<or>
    (f=inv__19  )\<or>
    (f=inv__20  )\<or>
    (f=inv__21  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__22  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__23  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__24  p__Inv4)\<or>
    (f=inv__25  )\<or>
    (f=inv__26  )\<or>
    (f=inv__27  )\<or>
    (f=inv__28  )\<or>
    (f=inv__29  )\<or>
    (f=inv__30  )\<or>
    (f=inv__31  )\<or>
    (f=inv__32  )\<or>
    (f=inv__33  )\<or>
    (f=inv__34  )\<or>
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
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__52  p__Inv4)\<or>
    (f=inv__53  )\<or>
    (f=inv__54  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__55  p__Inv4)\<or>
    (f=inv__56  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__57  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__58  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__59  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__60  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__61  p__Inv4)\<or>
    (f=inv__62  )\<or>
    (f=inv__63  )\<or>
    (f=inv__64  )\<or>
    (f=inv__65  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__66  p__Inv4)\<or>
    (f=inv__67  )\<or>
    (f=inv__68  )\<or>
    (f=inv__69  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__70  p__Inv4)\<or>
    (f=inv__71  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__72  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__73  p__Inv4)\<or>
    (f=inv__74  )\<or>
    (f=inv__75  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__76  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__77  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__78  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__79  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__80  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__81  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__82  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__83  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__84  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__85  p__Inv4)\<or>
    (f=inv__86  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__87  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__88  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__89  p__Inv4)\<or>
    (f=inv__90  )\<or>
    (f=inv__91  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__92  p__Inv4)\<or>
    (f=inv__93  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__94  p__Inv4)\<or>
    (f=inv__95  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__96  p__Inv4)\<or>
    (f=inv__97  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__98  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__99  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__100  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__101  p__Inv4)\<or>
    (f=inv__102  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__103  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__104  p__Inv4)\<or>
    (f=inv__105  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__106  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__107  p__Inv4)\<or>
    (f=inv__108  )\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__109  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__110  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__111  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__112  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__113  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__114  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__115  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__116  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__117  p__Inv4)\<or>
    (f=inv__118  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__119  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__120  p__Inv4)\<or>
    (f=inv__121  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__122  p__Inv4)\<or>
    (f=inv__123  )\<or>
    (f=inv__124  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__125  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__126  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__127  p__Inv4)\<or>
    (f=inv__128  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__129  p__Inv4)\<or>
    (f=inv__130  )\<or>
    (f=inv__131  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__132  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__133  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__134  p__Inv4)\<or>
    (f=inv__135  )\<or>
    (f=inv__136  )\<or>
    (f=inv__137  )\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__138  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__139  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__140  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__141  p__Inv4)\<or>
    (f=inv__142  )\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__143  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__144  p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__145  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__146  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__147  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__148  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__149  p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__150  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__151  p__Inv3 p__Inv4)\<or>
    (\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__152  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__3  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__3)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__4  p__Inv4)"
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
      assume d1: "(f=inv__7  )"
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
      assume d1: "(f=inv__10  )"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__14  p__Inv4)"
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
      assume d1: "(f=inv__16  )"
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
      assume d1: "(f=inv__19  )"
      have "formEval f s"
      apply (rule iniImply_inv__19)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__20  )"
      have "formEval f s"
      apply (rule iniImply_inv__20)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__21  )"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__23  p__Inv4)"
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
      assume d1: "(f=inv__30  )"
      have "formEval f s"
      apply (rule iniImply_inv__30)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__31  )"
      have "formEval f s"
      apply (rule iniImply_inv__31)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__32  )"
      have "formEval f s"
      apply (rule iniImply_inv__32)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__33  )"
      have "formEval f s"
      apply (rule iniImply_inv__33)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__34  )"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__52  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__55  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__57  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__57)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__58  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__58)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__59  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__61  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__66  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__66)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__67  )"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__70  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__70)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__71  )"
      have "formEval f s"
      apply (rule iniImply_inv__71)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__72  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__72)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__73  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__73)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__74  )"
      have "formEval f s"
      apply (rule iniImply_inv__74)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__75  )"
      have "formEval f s"
      apply (rule iniImply_inv__75)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__76  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__79  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__79)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__80  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__82  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__85  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__85)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__86  )"
      have "formEval f s"
      apply (rule iniImply_inv__86)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__87  p__Inv4)"
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
      assume d1: "(f=inv__90  )"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__92  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__92)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__93  )"
      have "formEval f s"
      apply (rule iniImply_inv__93)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__94  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__94)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__95  )"
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
      assume d1: "(f=inv__97  )"
      have "formEval f s"
      apply (rule iniImply_inv__97)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__98  p__Inv4)"
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
      assume d1: "(f=inv__102  )"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__104  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__104)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__105  )"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__107  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__107)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__108  )"
      have "formEval f s"
      apply (rule iniImply_inv__108)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__109  p__Inv3 p__Inv4)"
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
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__111  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__111)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__112  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__112)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__113  p__Inv3 p__Inv4)"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__119  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__119)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__120  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__120)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__121  )"
      have "formEval f s"
      apply (rule iniImply_inv__121)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__122  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__122)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__123  )"
      have "formEval f s"
      apply (rule iniImply_inv__123)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__124  )"
      have "formEval f s"
      apply (rule iniImply_inv__124)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__125  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__125)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__126  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__126)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__127  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__127)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__128  )"
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
      assume d1: "(f=inv__130  )"
      have "formEval f s"
      apply (rule iniImply_inv__130)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(f=inv__131  )"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__133  p__Inv4)"
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
      assume d1: "(f=inv__136  )"
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
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__138  p__Inv3 p__Inv4)"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__140  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__143  p__Inv4)"
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
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__146  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__146)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__147  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__147)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__148  p__Inv3 p__Inv4)"
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
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__150  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__150)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__151  p__Inv3 p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__151)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__152  p__Inv4)"
      have "formEval f s"
      apply (rule iniImply_inv__152)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

  ultimately show "formEval f s"
  by satx
qed

end
