theory n_g2k imports lemma_invs_on_rules on_inis
begin
lemma main:
assumes a1: "s \<in> reachableSet {andList (allInitSpecs N)} (rules N)"
and a2: "0 < N"
shows "\<forall> f. f \<in> (invariants N) --> formEval f s"
proof (rule newconsistentLemma)
show "newconsistent (invariants N) {andList (allInitSpecs N)} (rules N)"
proof (cut_tac a1, unfold newconsistent_def, rule conjI)
show "\<forall> f ini s. f \<in> (invariants N) --> ini \<in> {andList (allInitSpecs N)} --> formEval ini s --> formEval f s"
proof ((rule allI)+, (rule impI)+)
  fix f ini s
  assume b1: "f \<in> (invariants N)" and b2: "ini \<in> {andList (allInitSpecs N)}" and b3: "formEval ini s"
  have b4: "formEval (andList (allInitSpecs N)) s"
  apply (cut_tac b2 b3, simp) done
  show "formEval f s"
  apply (rule on_inis, cut_tac b1, assumption, cut_tac b2, assumption, cut_tac b3, assumption) done
qed
next show "\<forall> f r s. f \<in> invariants N --> r \<in> rules N --> invHoldForRule' s f r (invariants N)"
proof ((rule allI)+, (rule impI)+)
  fix f r s
  assume b1: "f \<in> invariants N" and b2: "r \<in> rules N"
  show "invHoldForRule' s f r (invariants N)"
  apply (rule invs_on_rules, cut_tac b1, assumption, cut_tac b2, assumption) done
qed
qed
next show "s \<in> reachableSet {andList (allInitSpecs N)} (rules N)"
  apply (metis a1) done
qed
end
