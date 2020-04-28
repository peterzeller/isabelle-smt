theory ex_proof_rules
  imports ex_lang
begin

section "Proof Rules"

text "We first define partial correctness of a program with pre- and post-conditions:"

definition correct :: "(state \<Rightarrow> bool) \<Rightarrow> stmt \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bool" ("\<Turnstile> {_} _ {_}") where
"\<Turnstile> {P} stmt {Q} \<equiv> \<forall>S. P S \<longrightarrow> \<not>steps S stmt None \<and> (\<forall>S'. steps S stmt (Some S') \<longrightarrow> Q S')"

lemma use_correct:
  assumes "\<Turnstile> {P} stmt {Q}"
    and "P S"
    and "steps S stmt Sf"
  shows "\<exists>S'. Sf = Some S' \<and> Q S'"
  using assms by (auto simp add: correct_def)
    (metis (full_types) not_None_eq)



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

lemma rule_if:
  assumes "\<Turnstile> {P1} t {Q}"
    and "\<Turnstile> {P2} f {Q}"
  shows "\<Turnstile> {\<lambda>S. case eval S c of Some (BoolVal b) \<Rightarrow> (if b then P1 else P2) S | _ \<Rightarrow> False } If c t f {Q}"
  using assms by (auto simp add: correct_def steps_big_if_iff split: option.splits val.splits elim: steps.cases)




lemma steps_while_induct:
  assumes "steps S (While c I b) Sf"
    and "P S"
    and loop: "\<And>S Sf. \<lbrakk>P S; eval S c = Some (BoolVal True); steps S b Sf\<rbrakk> \<Longrightarrow> \<exists>S'. Sf = Some S' \<and>  P S'"
    and cond_wf: "\<And>S. P S \<Longrightarrow> \<exists>b. eval S c = Some (BoolVal b)"
  shows "\<exists>S'. Sf = Some S' \<and> eval S' c = Some (BoolVal False) \<and> P S'"
proof -
  define stmt where "stmt \<equiv> While c I b"

  have "steps S stmt Sf"
    by (simp add: assms(1) stmt_def)

  have stmt: "stmt = While c I b \<and> P S \<or> (\<exists>b'. stmt = Seq b' (While c I b) \<and> (\<forall>Sf. steps S b' Sf \<longrightarrow> (\<exists>S'. Sf = Some S' \<and>  P S')))" 
    using stmt_def `P S` by simp

  from `steps S stmt Sf` and stmt
  have "\<exists>S'. Sf = Some S' \<and> eval S' c = Some (BoolVal False) \<and> P S'"
  proof (induct rule: steps.induct)
    case (final S S')
    then show ?case
      by (auto split: option.splits val.splits bool.splits step_res.splits)


  next
    case (nonfinal S stmt S' stmt' S'')

    have IH1: "stmt' = While c I b \<Longrightarrow> P S'  \<Longrightarrow>
      \<exists>S'. S'' = Some S' \<and> eval S' c = Some (BoolVal False) \<and> P S'"
      using nonfinal.hyps by blast


    have IH2: "\<exists>b'. stmt' = Seq b' (While c I b) \<and> (\<forall>Sf. steps S' b' Sf \<longrightarrow> (\<exists>S'. Sf = Some S' \<and> P S')) \<Longrightarrow>
      \<exists>S'. S'' = Some S' \<and> eval S' c = Some (BoolVal False) \<and> P S'"
      using nonfinal.hyps by blast

    have IH2': "\<And>b'. stmt' = Seq b' (While c I b) \<Longrightarrow> (\<And>Sf. steps S' b' Sf \<Longrightarrow> (\<exists>S'. Sf = Some S' \<and> P S')) \<Longrightarrow>
      \<exists>S'. S'' = Some S' \<and> eval S' c = Some (BoolVal False) \<and> P S'"
      using nonfinal.hyps by blast

    from `stmt = While c I b \<and> P S \<or>  (\<exists>b'. stmt = Seq b' (While c I b) \<and> (\<forall>Sf. steps S b' Sf \<longrightarrow> (\<exists>S'. Sf = Some S' \<and> P S')))`
    show ?case
    proof (rule disjE; use nothing in \<open>elim conjE exE\<close>)
      assume "stmt = While c I b" and "P S"
      show "\<exists>S'. S'' = Some S' \<and> eval S' c = Some (BoolVal False) \<and> P S'"
      proof (rule IH2)


        from `step S stmt = NonFinal S' stmt'` and `stmt = While c I b`
        show "\<exists>b'. stmt' = Seq b' (While c I b) \<and> (\<forall>Sf. steps S' b' Sf \<longrightarrow> (\<exists>S'. Sf = Some S' \<and> P S'))"
          apply (auto split: option.splits val.splits bool.splits)
          using \<open>P S\<close> loop by blast+
      qed
    next
      fix b'
      assume stmt_def: "stmt = Seq b' (While c I b)"
        and P_S': "\<forall>Sf. steps S b' Sf \<longrightarrow> (\<exists>S'. Sf = Some S' \<and> P S')"


      from `step S stmt = NonFinal S' stmt'`
      have "step S b' = Final S' \<and> stmt' = While c I b
          \<or> (\<exists>b''. step S b' = NonFinal S' b'' \<and> stmt' = Seq b'' (While c I b))"
        by (auto simp add: stmt_def split: step_res.splits)

      thus "\<exists>S'. S'' = Some S' \<and> eval S' c = Some (BoolVal False) \<and> P S'"
      proof (rule disjE; use nothing in \<open>elim conjE exE\<close>)
        assume a0: "step S b' = Final S'"
          and a1: "stmt' = While c I b"

        show "\<exists>S'. S'' = Some S' \<and> eval S' c = Some (BoolVal False) \<and> P S'"
          using a1
        proof (rule IH1)
          from P_S'
          show "P S'"
            by (metis a0 option.sel steps.simps)
        qed
      next
        fix b''
        assume a0: "step S b' = NonFinal S' b''"
          and a1: "stmt' = Seq b'' (While c I b)"

        show "\<exists>S'. S'' = Some S' \<and> eval S' c = Some (BoolVal False) \<and> P S'"
          using a1
        proof (rule IH2')
          show "\<And>Sf. steps S' b'' Sf \<Longrightarrow> \<exists>S'. Sf = Some S' \<and> P S'"
            by (simp add: P_S' a0 steps.nonfinal)
        qed
      qed
    qed
  next
    case (error S)
    then show ?case 
      apply (auto split: option.splits val.splits bool.splits step_res.splits)
      using cond_wf apply fastforce
      using cond_wf apply fastforce
      using loop steps.error by fastforce
  qed

  thus ?thesis
    by simp
qed

lemma rule_while:
  assumes check_body: "\<Turnstile> {P} b {\<lambda>S. eval S I = Some (BoolVal True)}"
    and condition_wf: "\<And>S. eval S I = Some (BoolVal True) \<Longrightarrow> \<exists>b. eval S c = Some (BoolVal b)"
    and inv_P: "\<And>S. eval S I = Some (BoolVal True) \<Longrightarrow> eval S c = Some (BoolVal True) \<Longrightarrow> P S"
    and inv_Q: "\<And>S. eval S I = Some (BoolVal True) \<Longrightarrow> eval S c = Some (BoolVal False) \<Longrightarrow> Q S"
  shows "\<Turnstile> {\<lambda>S. eval S I = Some (BoolVal True)} While c I b {Q}"
proof -

  have h: "\<exists>S'. Sf = Some S' \<and> eval S' c = Some (BoolVal False) \<and> eval S' I = Some (BoolVal True)"
    if steps: "steps S (While c I b) Sf"
      and inv_init: "eval S I = Some (BoolVal True)"
    for S Sf
  proof (rule steps_while_induct[OF steps])
    show "eval S I = Some (BoolVal True)"
      using inv_init by simp

    show "\<exists>S'. Sf = Some S' \<and> eval S' I = Some (BoolVal True)"
      if c0: "eval S I = Some (BoolVal True)"
        and c1: "eval S c = Some (BoolVal True)"
        and c2: "steps S b Sf"
      for  S Sf
    proof -

      have "P S"
        by (simp add: c0 c1 inv_P)


      from use_correct[OF check_body `P S` `steps S b Sf`]
      show "\<exists>S'. Sf = Some S' \<and> eval S' I = Some (BoolVal True)"
        by blast
    qed


    show "\<exists>b. eval S c = Some (BoolVal b)"
      if c0: "eval S I = Some (BoolVal True)"
      for  S
      by (simp add: condition_wf that)
  qed

  show ?thesis
    using h inv_Q  by (auto simp add: correct_def)
qed


end