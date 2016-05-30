(*  Title:      HOL/Auth/n_german_on_ini.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_german Protocol Case Study*} 

theory n_german_on_ini imports n_german_base
begin
lemma iniImply_inv__1:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__1  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__2:
assumes a1: "(f=inv__2  )"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__3:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__3  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__4:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__4  p__Inv3 p__Inv4)"
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
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__7  p__Inv4)"
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
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__10  p__Inv3 p__Inv4)"
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
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__14  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__15:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__15  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__16:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__16  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__17:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__17  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__18:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__18  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__19:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__19  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__20:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__20  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__21:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__21  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__22:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__22  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__23:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__23  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__24:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__24  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__25:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__25  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__26:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__26  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__27:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__27  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__28:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__28  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__29:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__29  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__30:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__30  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__31:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__31  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__32:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__32  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__33:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__33  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__34:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__34  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__35:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__35  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__36:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__36  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__37:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__37  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__38:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__38  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__39:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__39  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__40:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__40  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__41:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__41  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__42:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__42  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__43:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__43  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__44:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__44  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__45:
assumes a1: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__45  p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__46:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__46  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__47:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__47  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__48:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__48  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__49:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__49  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__50:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__50  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__51:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__51  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__52:
assumes a1: "(\<exists> p__Inv3 p__Inv4. p__Inv3\<le>N\<and>p__Inv4\<le>N\<and>p__Inv3~=p__Inv4\<and>f=inv__52  p__Inv3 p__Inv4)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto
end
