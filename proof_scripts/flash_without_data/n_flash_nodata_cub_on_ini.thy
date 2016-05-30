(*  Title:      HOL/Auth/n_flash_nodata_cub_on_ini.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_flash_nodata_cub Protocol Case Study*} 

theory n_flash_nodata_cub_on_ini imports n_flash_nodata_cub_base
begin
lemma iniImply_inv__1:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__2:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__2  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__3:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__3  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__4:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__4  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__5:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__5  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__6:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__6  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__7:
assumes a1: "(f=inv__7  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__8:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__8  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__9:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__9  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__10:
assumes a1: "(f=inv__10  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__11:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__11  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__12:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__12  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__13:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__13  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__14:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__14  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__15:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__15  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__16:
assumes a1: "(f=inv__16  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__17:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__17  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__18:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__18  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__19:
assumes a1: "(f=inv__19  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__20:
assumes a1: "(f=inv__20  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__21:
assumes a1: "(f=inv__21  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__22:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__22  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__23:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__23  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__24:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__24  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__25:
assumes a1: "(f=inv__25  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__26:
assumes a1: "(f=inv__26  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__27:
assumes a1: "(f=inv__27  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__28:
assumes a1: "(f=inv__28  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__29:
assumes a1: "(f=inv__29  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__30:
assumes a1: "(f=inv__30  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__31:
assumes a1: "(f=inv__31  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__32:
assumes a1: "(f=inv__32  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__33:
assumes a1: "(f=inv__33  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__34:
assumes a1: "(f=inv__34  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__35:
assumes a1: "(f=inv__35  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__36:
assumes a1: "(f=inv__36  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__37:
assumes a1: "(f=inv__37  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__38:
assumes a1: "(f=inv__38  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__39:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__39  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__40:
assumes a1: "(f=inv__40  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__41:
assumes a1: "(f=inv__41  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__42:
assumes a1: "(f=inv__42  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__43:
assumes a1: "(f=inv__43  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__44:
assumes a1: "(f=inv__44  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__45:
assumes a1: "(f=inv__45  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__46:
assumes a1: "(f=inv__46  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__47:
assumes a1: "(f=inv__47  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__48:
assumes a1: "(f=inv__48  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__49:
assumes a1: "(f=inv__49  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__50:
assumes a1: "(f=inv__50  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__51:
assumes a1: "(f=inv__51  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__52:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__52  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__53:
assumes a1: "(f=inv__53  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__54:
assumes a1: "(f=inv__54  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__55:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__55  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__56:
assumes a1: "(f=inv__56  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__57:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__57  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__58:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__58  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__59:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__59  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__60:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__60  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__61:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__61  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__62:
assumes a1: "(f=inv__62  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__63:
assumes a1: "(f=inv__63  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__64:
assumes a1: "(f=inv__64  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__65:
assumes a1: "(f=inv__65  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__66:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__66  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__67:
assumes a1: "(f=inv__67  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__68:
assumes a1: "(f=inv__68  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__69:
assumes a1: "(f=inv__69  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__70:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__70  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__71:
assumes a1: "(f=inv__71  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__72:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__72  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__73:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__73  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__74:
assumes a1: "(f=inv__74  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__75:
assumes a1: "(f=inv__75  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__76:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__76  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__77:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__77  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__78:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__78  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__79:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__79  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__80:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__80  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__81:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__81  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__82:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__82  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__83:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__83  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__84:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__84  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__85:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__85  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__86:
assumes a1: "(f=inv__86  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__87:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__87  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__88:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__88  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__89:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__89  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__90:
assumes a1: "(f=inv__90  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__91:
assumes a1: "(f=inv__91  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__92:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__92  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__93:
assumes a1: "(f=inv__93  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__94:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__94  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__95:
assumes a1: "(f=inv__95  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__96:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__96  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__97:
assumes a1: "(f=inv__97  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__98:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__98  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__99:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__99  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__100:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__100  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__101:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__101  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__102:
assumes a1: "(f=inv__102  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__103:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__103  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__104:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__104  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__105:
assumes a1: "(f=inv__105  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__106:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__106  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__107:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__107  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__108:
assumes a1: "(f=inv__108  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__109:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__109  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__110:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__110  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__111:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__111  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__112:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__112  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__113:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__113  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__114:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__114  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__115:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__115  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__116:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__116  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__117:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__117  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__118:
assumes a1: "(f=inv__118  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__119:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__119  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__120:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__120  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__121:
assumes a1: "(f=inv__121  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__122:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__122  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__123:
assumes a1: "(f=inv__123  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__124:
assumes a1: "(f=inv__124  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__125:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__125  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__126:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__126  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__127:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__127  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__128:
assumes a1: "(f=inv__128  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__129:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__129  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__130:
assumes a1: "(f=inv__130  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__131:
assumes a1: "(f=inv__131  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__132:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__132  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__133:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__133  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__134:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__134  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__135:
assumes a1: "(f=inv__135  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__136:
assumes a1: "(f=inv__136  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__137:
assumes a1: "(f=inv__137  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__138:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__138  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__139:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__139  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__140:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__140  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__141:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__141  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__142:
assumes a1: "(f=inv__142  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__143:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__143  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__144:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__144  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__145:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__145  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__146:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__146  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__147:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__147  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__148:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__148  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__149:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__149  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__150:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__150  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__151:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__151  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__152:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__152  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto
end
