theory smt_theory_array
  imports smt_theories
begin

definition "t_array \<equiv> TypeName ''array''"
definition "c_select \<equiv> ConstName ''select''"
definition "c_store \<equiv> ConstName ''store''"

definition array_sig :: signature where
"array_sig \<equiv> \<lparr>
  function_type = [c_select \<mapsto> undefined, c_store  \<mapsto> undefined],
  type_arity = [t_array \<mapsto> 2]
\<rparr>"


definition is_array_model :: "'u::universe interpr \<Rightarrow> bool" where
"is_array_model I \<equiv> 
  \<forall>s1 s2.
  let arrays = i_elements I (CType t_array [s1, s2])
  in 
  (\<forall>a\<in>arrays. \<forall>i\<in>i_elements I s1. \<forall>e\<in>i_elements I s2.
    i_evaluate_const I c_select [i_evaluate_const I c_store [a, i, e], i] = e)
  \<and> (\<forall>a\<in>arrays. \<forall>i\<in>i_elements I s1. \<forall>j\<in>i_elements I s1. \<forall>e\<in>i_elements I s2.
      i \<noteq> j \<longrightarrow> (i_evaluate_const I c_select [i_evaluate_const I c_store [a, i, e], j])
                = i_evaluate_const I c_select [a, j])
  \<and> (\<forall>a\<in>arrays. \<forall>b\<in>arrays. 
      (\<forall>i\<in>i_elements I s1. i_evaluate_const I c_select [a, i] = i_evaluate_const I c_select [b, i]
        \<longrightarrow> a = b))
"

definition array_theory :: "'u::universe smt_theory" where
"array_theory \<equiv> \<lparr>
  t_signature = array_sig,
  t_models = Collect is_array_model
\<rparr>"


end