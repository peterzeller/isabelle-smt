theory ex_lang
  imports Main
    "HOL-Library.Monad_Syntax"
begin

section \<open>Language Definition\<close>

subsection \<open>Abstract Syntax\<close>

text \<open>We first define the abstract syntax of our language:\<close>

datatype builtin = 
    Plus 
  | Minus 
  | Times 
  | Div 
  | Mod
  | And 
  | Or
  | Not
  | Neg
  | Eq
  | Less
  | LessEq
  | Greater
  | GreaterEq

type_synonym var = string

datatype val =
    IntVal int
  | BoolVal bool

datatype expr = 
    Builtin builtin "expr list"
  | Const val
  | VarRead var

datatype stmt =
    Assert expr
  | Assume expr
  | Assign var expr
  | If expr stmt stmt
  | While expr stmt
  | Seq stmt stmt


subsection \<open>Semantics\<close>

text \<open>We now define the semantics of the language using a small step operational semantics.\<close>



record state =
  varState :: "var \<rightharpoonup> val"


value "Some (5::int) \<bind> (\<lambda>x. Some (x +  1))"

value "those ([Some 1, Some 2]::int option list)"

find_consts "'a list \<Rightarrow> 'b list option"

definition eval_builtin  :: "builtin \<Rightarrow> val list \<rightharpoonup> val" where
"eval_builtin b es \<equiv> case (b,es) of
  (Plus, [IntVal x,IntVal y]) \<Rightarrow> Some (IntVal (x+y))
| (Minus, [IntVal x,IntVal y]) \<Rightarrow> Some (IntVal (x-y))
| (Times, [IntVal x,IntVal y]) \<Rightarrow> Some (IntVal (x*y))
| (Div, [IntVal x,IntVal y]) \<Rightarrow> (if y = 0 then None else Some (IntVal (x div y)))
| (Mod, [IntVal x,IntVal y]) \<Rightarrow> (if y = 0 then None else Some (IntVal (x mod y)))
| (And, [BoolVal x,BoolVal y]) \<Rightarrow> Some (BoolVal (x \<and> y))
| (Or, [BoolVal x,BoolVal y]) \<Rightarrow> Some (BoolVal (x \<or> y))
| (Not, [BoolVal x]) \<Rightarrow> Some (BoolVal (\<not>x))
| (Neg, [IntVal x]) \<Rightarrow> Some (IntVal (-x))
| (Eq, [x, y]) \<Rightarrow> Some (BoolVal (x=y))
| (Less, [IntVal x,IntVal y]) \<Rightarrow> Some (BoolVal (x<y))
| (LessEq, [IntVal x,IntVal y]) \<Rightarrow> Some (BoolVal (x\<le>y))
| (Greater, [IntVal x,IntVal y]) \<Rightarrow> Some (BoolVal (x>y))
| (GreaterEq, [IntVal x,IntVal y]) \<Rightarrow> Some (BoolVal (x\<ge>y))
| _ \<Rightarrow> None"


fun eval :: "state \<Rightarrow> expr \<rightharpoonup> val" where
  "eval S (Builtin b es) = those (map (eval S) es) \<bind> eval_builtin b"
| "eval S (VarRead v) = varState S v"
| "eval S (Const v) = Some v"


definition "updateVar S x v \<equiv> S\<lparr>varState := (varState S)(x \<mapsto> v)\<rparr>" 

datatype step_res = Final state | NonFinal state stmt | Error | Invalid

fun step :: "state \<Rightarrow> stmt \<Rightarrow> step_res" where
  "step S (Assert e) = (case eval S e of Some (BoolVal True) \<Rightarrow> Final S | _ \<Rightarrow> Error)"
| "step S (Assume e) = (case eval S e of Some (BoolVal True) \<Rightarrow> Final S | _ \<Rightarrow> Invalid)"
| "step S (Assign x e) = (case eval S e of Some v \<Rightarrow> Final (updateVar S x v) | _ \<Rightarrow> Error)"
| "step S (If c t f) = (case eval S c of Some (BoolVal True) \<Rightarrow> NonFinal S t
                                       | Some (BoolVal False) \<Rightarrow> NonFinal S f 
                                       | _ \<Rightarrow> Error)"
| "step S (While c b) = (case eval S c of Some (BoolVal True) \<Rightarrow> NonFinal S (Seq b (While c b))
                                       | Some (BoolVal False) \<Rightarrow> Final S 
                                       | _ \<Rightarrow> Error)"
| "step S (Seq a b) = (case step S a of Final S' \<Rightarrow> NonFinal S' b
                                      | NonFinal S' a' \<Rightarrow> NonFinal S' (Seq a' b) 
                                      | Error \<Rightarrow> Error 
                                      | Invalid \<Rightarrow> Invalid)"


inductive steps :: "state \<Rightarrow> stmt \<Rightarrow> state option \<Rightarrow> bool" where
  final: "step S stmt = Final S' \<Longrightarrow>  steps S stmt (Some S')"
| nonfinal: "\<lbrakk>step S stmt = NonFinal S' stmt'; steps S' stmt' S''\<rbrakk> \<Longrightarrow> steps S stmt S''"
| error: "step S stmt = Error \<Longrightarrow> steps S stmt None"


text "We also show some big step forms of the rules:"

lemma steps_big_seq1:
  assumes "steps S a S1"
    and "S1 = Some S'"
    and "steps S' b S''"
  shows "steps S (Seq a b) S''"
  using assms proof (induct rule: steps.induct)
case (final S stmt S')
  then show ?case
    using nonfinal by auto
next
  case (nonfinal S stmt S' stmt' S'')
  then show?case 
    by (metis step.simps(6) step_res.simps(16) steps.simps)
next
  case (error S stmt)
  then show ?case 
    by blast
qed

lemma steps_big_seq:
  assumes "steps S a (Some S')"
    and "steps S' b S''"
  shows "steps S (Seq a b) S''"
  using assms(1) assms(2) steps_big_seq1 by auto

lemma steps_big_seq_None1:
  assumes "steps S a S'"
    and "S' = None"
  shows "steps S (Seq a b) None"
  using assms proof (induct rule: steps.induct)
  case (final S stmt S')
  then show ?case 
    by auto
next
  case (nonfinal S stmt S' stmt' S'')
  then show ?case
    by (simp add: steps.nonfinal)
next
  case (error S stmt)
  then show ?case 
    using steps.error by auto
qed


lemma steps_big_seq_None:
  assumes "steps S a None"
  shows "steps S (Seq a b) None"
  using assms steps_big_seq_None1 by auto

lemma step_seq:
  assumes "step S (Seq a b) = Final S'"
  shows "step S a = Final S'"
  using assms by (auto split: step_res.splits)


lemma steps_big_seq_iff:
  shows "steps S (Seq a b) S'' \<longleftrightarrow> (steps S a None \<and> S'' = None \<or> (\<exists>S'. steps S a (Some S') \<and> steps S' b S''))"
proof (rule iffI conjI; (elim disjE conjE exE)?)
  assume a0: "steps S a None"
    and a1: "S'' = None"

  show "steps S (Seq a b) S''"
    by (simp add: a0 a1 steps_big_seq_None)
next
  fix S'
  assume a0: "steps S a (Some S')"
    and a1: "steps S' b S''"

  show "steps S (Seq a b) S''"
    using a0 a1 steps_big_seq1 by blast
next
  assume a0: "steps S (Seq a b) S''"

  define stmt where "stmt \<equiv> Seq a b"

  have "steps S stmt S''"
    by (simp add: a0 stmt_def)

  from `steps S stmt S''` stmt_def
  have "\<exists>S'. steps S a S' \<and> (case S' of Some S' \<Rightarrow> steps S' b S'' | None \<Rightarrow> S'' = None)"
  proof (induct  arbitrary: a rule: steps.induct)
    case (final S S')
    then show ?case 
      using step_seq by force
  next
    case (nonfinal S S' stmt' S'')

    from `step S (Seq a b) = NonFinal S' stmt'`
    show ?case
      apply (auto split: step_res.splits)
      using final nonfinal.hyps(2) apply fastforce
      using nonfinal.hyps(3) steps.nonfinal by blast
  next
    case (error S)
    then show ?case 
      apply (auto split: step_res.splits)
      using steps.error by fastforce
  qed


  from this
  obtain S' where "steps S a S'"
    and "case S' of Some S' \<Rightarrow> steps S' b S'' | None \<Rightarrow> S'' = None"
    by blast

  from this
  show "steps S a None \<and> S'' = None \<or> (\<exists>S'. steps S a (Some S') \<and> steps S' b S'')"
    using case_optionE by blast
qed
   
                              

lemma steps_big_if_True:
  assumes "eval S c = Some (BoolVal True)"
    and "steps S t S'"
  shows "steps S (If c t f) S'"
  using assms nonfinal steps_big_seq1 by auto

lemma steps_big_if_False:
  assumes "eval S c = Some (BoolVal False)"
    and "steps S f S'"
  shows "steps S (If c t f) S'"
  using assms nonfinal steps_big_seq1 by auto


lemma steps_big_while_True:
  assumes "eval S c = Some (BoolVal True)"
    and "steps S b (Some S')"
    and "steps S' (While c b) S''"
  shows "steps S (While c b) S''"
  using assms nonfinal steps_big_seq1 by auto

lemma steps_big_while_False:
  assumes "eval S c = Some (BoolVal False)"
  shows "steps S (While c b) (Some S)"
  by (simp add: assms final)




end