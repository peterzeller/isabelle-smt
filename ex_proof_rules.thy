theory ex_proof_rules
  imports ex_lang
begin

section "Proof Rules"

text "We first define partial correctness of a program with pre- and post-conditions:"

definition correct :: "(state \<Rightarrow> bool) \<Rightarrow> stmt \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bool" ("\<Turnstile> {_} _ {_}") where
"\<Turnstile> {P} stmt {Q} \<equiv> \<forall>S. P S \<longrightarrow> \<not>steps S stmt None \<and> (\<forall>S'. steps S stmt (Some S') \<longrightarrow> Q S')"


subsection "Weakest precondition rules"


lemma rule_assign:
  shows "\<Turnstile> {\<lambda>S. case eval S e of Some v \<Rightarrow> Q (updateVar S x v) | None \<Rightarrow> False} Assign x e {Q}"
  by (auto simp add: correct_def split: option.splits)
    (use steps.cases in \<open>fastforce+\<close>)

lemma rule_seq:
  assumes "\<Turnstile> {Q} b {R}"
    and "\<Turnstile> {P} a {Q}"
  shows "\<Turnstile> {P} Seq a b {R}"
  using assms by (auto simp add: correct_def steps_big_seq_iff)






end