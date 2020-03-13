section "SMT Theories"
theory smt_theories
  imports smt_base
begin

record 'u smt_theory =
  t_signature :: signature
  t_models :: "'u model set"

text "It is possible to define theories with compatible signatures:"

definition combine_theories where
"combine_theories t1 t2 \<equiv> do {
  sig \<leftarrow> combine_signatures (t_signature t1) (t_signature t2);
  Some \<lparr>
    t_signature = sig,
    t_models = (t_models t1 \<inter> t_models t2)
  \<rparr>
}"

text "Next, we define satisfiability with respect to a theory. "


end