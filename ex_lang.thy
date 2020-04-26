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
  | Assign var expr
  | If expr expr stmt stmt
  | While expr stmt
  | Seq expr expr


subsection \<open>Semantics\<close>

text \<open>We now define the semantics of the language using a big step operational semantics.\<close>



record state =
  varState :: "var \<rightharpoonup> val"
  error :: "bool"


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

definition "withError S \<equiv> S\<lparr>error := True\<rparr>"

definition "updateVar S x v \<equiv> S\<lparr>varState := (varState S)(x \<mapsto> v)\<rparr>" 

inductive step :: "state \<Rightarrow> stmt \<Rightarrow> state \<Rightarrow> bool" where
assert_true: 
"eval S e = Some (BoolVal True) \<Longrightarrow> step S (Assert e) S"
| assert_false:
"eval S e \<noteq> Some (BoolVal True) \<Longrightarrow> step S (Assert e) (withError S)"
| assign:
"eval S e = Some v \<Longrightarrow> step S (Assign x e) (updateVar S x v)" 


end