section "SMT Semantics"
theory smt_semantics
  imports smt_base
begin

text \<open>We first define interprtations. 
Interpretations assign a set to every type, a value to every variable, and they 
can interpret function calls.
We use a type parameter 'u for the universe used in the interpretation.
An universe must at least include the Boolean values, a constraint we impose using a type class.
\<close>

class universe =
  fixes from_bool :: "bool \<Rightarrow> 'a"
  fixes to_bool :: "'a \<Rightarrow> bool"
  assumes "to_bool (from_bool b) = b"


  

record 'u::universe interpr =
  i_elements :: "ctype \<Rightarrow> 'u set"
  i_evaluate_const :: "constName \<Rightarrow> 'u list \<Rightarrow> 'u"
  i_var_value :: "varName \<Rightarrow> 'u"

definition withVar ("_ with _ := _") where
"I with v := x \<equiv> I\<lparr>i_var_value := (i_var_value I)(v := x)\<rparr>"

definition 
"evaluate_quantifier q \<equiv> case q of Forall \<Rightarrow> Ball | Exists \<Rightarrow> Bex"

definition
"evaluate_op op \<equiv> case op of
   And \<Rightarrow> (\<lambda>x y. from_bool (to_bool x \<and> to_bool y))
 | Or \<Rightarrow> (\<lambda>x y. from_bool (to_bool x \<or> to_bool y))
 | Implies \<Rightarrow> (\<lambda>x y. from_bool (to_bool x \<longrightarrow> to_bool y))
 | Eq \<Rightarrow> (\<lambda>x y. from_bool (x = y))"


fun evaluate :: "'u::universe interpr \<Rightarrow> s_term \<Rightarrow> 'u" where
  "evaluate I (Var v) = i_var_value I v"
| "evaluate I (Apply f es) = i_evaluate_const I f (map (evaluate I) es)"
| "evaluate I (Quantifier q t v e) = from_bool (evaluate_quantifier q  (i_elements I t) (\<lambda>x. to_bool (evaluate (I with v := x) e)))"
| "evaluate I (BinaryB l op r) = evaluate_op op (evaluate I l) (evaluate I r)"
| "evaluate I (Neg e) = from_bool (\<not>to_bool (evaluate I e))"
| "evaluate I (BoolConst v) = from_bool v"



end