section "The Theory of Integers"

theory smt_theory_ints
  imports smt_theories
    num_string_convert
begin

definition "t_int \<equiv> TypeName ''int''"
definition "c_negate \<equiv> ConstName ''negate''"
definition "c_minus \<equiv> ConstName ''minus''"
definition "c_plus \<equiv> ConstName ''plus''"
definition "c_times \<equiv> ConstName ''times''"
definition "c_div \<equiv> ConstName ''div''"
definition "c_mod \<equiv> ConstName ''mod''"
definition "c_abs \<equiv> ConstName ''abs''"
definition "c_lesseq \<equiv> ConstName ''lesseq''"
definition "c_less \<equiv> ConstName ''less''"
definition "c_greater \<equiv> ConstName ''greater''"
definition "c_greatereq \<equiv> ConstName ''greatereq''"

abbreviation "vt_int \<equiv> VType t_int []"

definition "numerals s \<equiv> 
  if is_nat_string (constName_name s) then Some (FunctionType [] vt_int) else None"

definition int_sig :: signature where
"int_sig \<equiv> \<lparr>
  function_type = [
    c_negate \<mapsto> FunctionType [vt_int] vt_int,
    c_minus \<mapsto> FunctionType [vt_int, vt_int] vt_int,
    c_plus \<mapsto> FunctionType [vt_int, vt_int] vt_int,
    c_times \<mapsto> FunctionType [vt_int, vt_int] vt_int,
    c_div \<mapsto> FunctionType [vt_int, vt_int] vt_int,
    c_mod \<mapsto> FunctionType [vt_int, vt_int] vt_int,
    c_abs \<mapsto> FunctionType [vt_int] vt_int,
    c_lesseq \<mapsto> FunctionType [vt_int, vt_int] VBool,
    c_less \<mapsto> FunctionType [vt_int, vt_int] VBool,
    c_greater \<mapsto> FunctionType [vt_int, vt_int] VBool,
    c_greatereq \<mapsto> FunctionType [vt_int, vt_int] VBool
  ] ++ numerals,
  type_arity = [t_int \<mapsto> 0]
\<rparr>"



text "Isabelles div and mod are not defined according to Boute's Euclidean definition,
  so we need to defined our own variants that work according to the SMT spec."

definition divp :: "int \<Rightarrow> int \<Rightarrow> int"  (infixl "divp" 70) where
"m divp n \<equiv> if m mod n < 0 then m div n + 1  else m div n"

definition modp :: "int \<Rightarrow> int \<Rightarrow> int"  (infixl "modp" 70) where
"m modp n \<equiv> let r = m mod n in if r < 0 then r + abs n else r"

lemma correct_int_model:
  fixes n :: int
  assumes "n\<noteq>0"
    and "q = m divp n"
    and "r = m modp n"
  shows "m = n*q + r"
    and "0 \<le> r"
    and "r \<le> abs n - 1"
  using assms by (auto simp add: divp_def modp_def algebra_simps split: if_splits,
      (smt Euclidean_Division.pos_mod_sign abs_mod_less)+)


definition is_iso1 where
"is_iso1 I t f g \<equiv> \<forall>x. inv t (i_evaluate_const I f [t x]) = g x"

definition is_iso2 where
"is_iso2 I t f g \<equiv> \<forall>x y. inv t (i_evaluate_const I f [t x, t y]) = g x y"

definition is_iso2b where
"is_iso2b I t f g \<equiv> \<forall>x y. to_bool (i_evaluate_const I f [t x, t y]) = g x y"

definition is_int_model :: "'u::universe interpr \<Rightarrow> bool" where
"is_int_model I \<equiv> 
  \<exists>t::int\<Rightarrow>'u. bij t
  \<and> is_iso1 I t c_negate (\<lambda>i. - i)
  \<and> is_iso1 I t c_abs abs
  \<and> is_iso2 I t c_plus (+)
  \<and> is_iso2 I t c_minus (-)
  \<and> is_iso2 I t c_times (*)
  \<and> is_iso2 I t c_div (divp)
  \<and> is_iso2 I t c_mod (modp)
  \<and> is_iso2b I t c_lesseq (\<le>)
  \<and> is_iso2b I t c_less (<)
  \<and> is_iso2b I t c_greatereq (\<ge>)
  \<and> is_iso2b I t c_greater (>)
  \<and> (\<forall>c. is_nat_string c \<longrightarrow> i_evaluate_const I (ConstName c) [] = t (int (string_to_nat c)))
"

definition int_theory :: "'u::universe smt_theory" where
"int_theory \<equiv> \<lparr>
  t_signature = int_sig,
  t_models = Collect is_int_model
\<rparr>"


end