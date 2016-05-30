(*  Title:      HOL/Auth/n_moesi_on_ini.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_moesi Protocol Case Study*} 

theory n_moesi_on_ini imports n_moesi_base
begin
lemma iniImply_inv__1:
assumes a1: "(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__1  p__Inv0 p__Inv2)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__2:
assumes a1: "(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__2  p__Inv0 p__Inv2)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto

lemma iniImply_inv__3:
assumes a1: "(\<exists> p__Inv0 p__Inv2. p__Inv0\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv2\<and>f=inv__3  p__Inv0 p__Inv2)"
and a2: "formEval (andList (allInitSpecs N)) s"
shows "formEval f s"
using a1 a2 by auto
end
