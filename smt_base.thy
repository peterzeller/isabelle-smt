theory smt_base
  imports
    Main
begin

datatype typeName = TypeName string
datatype varName = VarName string
datatype constName = ConstName string

datatype quantifier = Forall | Exists

datatype operator = And | Or | Implies | Eq

datatype ctype = Bool | CType typeName (type_args:"ctype list")
datatype vtype = VBool | VType typeName (type_args:"vtype list") | TypeVar varName

text "Function types can quantify over a set of variables"
datatype functionType = FunctionType "vtype list" vtype

datatype s_term =
    Var varName
  | Apply constName (args:"s_term list")
  | Quantifier quantifier "ctype" varName "s_term"
  | BinaryB "s_term" operator  "s_term"
  | Neg "s_term"
  | BoolConst bool


record signature =
  function_type :: "constName \<rightharpoonup> functionType"
  type_arity :: "typeName \<rightharpoonup> nat"

record 'u model =
  type_members :: "vtype \<Rightarrow> 'u set"
  interpret_func :: "constName \<Rightarrow> 'u list \<rightharpoonup> 'u" 

datatype 'a result = Ok 'a | Err string

definition "is_ok x = (case x of Ok _ \<Rightarrow> True | Err _ \<Rightarrow> False)"
definition "the_result x =  (case x of Ok r \<Rightarrow> r | Err _ \<Rightarrow> undefined)"

class "show" =
  fixes "show" :: "'a \<Rightarrow> string"

definition appendR (infixl "@." 66) where
"s @. x \<equiv> s @ show x"

definition appendL (infixr ".@" 67) where
"s .@ x \<equiv> show s @ x"



fun printSep where
"printSep s [] = ''''"
| "printSep s [x] = show x"
| "printSep s (x#xs) = show x @ s @ printSep s xs"


instantiation char :: "show" begin
definition "show_char \<equiv> (\<lambda>x::char. [x])"
instance by standard
end


instantiation list :: ("show") "show" begin
definition "show_list \<equiv> printSep ''''"
instance by standard
end

instantiation vtype :: "show" begin
definition "show \<equiv> (\<lambda>x::vtype. ''vtype'')"
instance by standard
end

instantiation typeName :: "show" begin
definition "show_typeName \<equiv> (\<lambda>x. case x of TypeName n \<Rightarrow> n)"
instance by standard
end


fun print_ctype where
"print_ctype Bool = ''Bool''"
| "print_ctype (CType v []) = show v"
| "print_ctype (CType v va) = v .@ ''<'' @ printSep '','' (map print_ctype va) @ ''>'' "

instantiation ctype :: "show" begin
definition "show_ctype \<equiv> print_ctype"
instance by standard
end

instantiation s_term :: "show" begin
definition "show_s_term \<equiv> (\<lambda>x::s_term. ''s_term'')"
instance by standard
end


instantiation varName :: "show" begin
definition "show_varName \<equiv> (\<lambda>x. case x of VarName n \<Rightarrow> n)"
instance by standard
end

instantiation constName :: "show" begin
definition "show_constName \<equiv> (\<lambda>x. case x of ConstName n \<Rightarrow> n)"
instance by standard
end




instantiation option :: ("show") "show" begin
definition "show_option \<equiv> (\<lambda>x. case x of Some x \<Rightarrow> ''Some '' @. x | None \<Rightarrow> ''None'' )"
instance by standard
end

instantiation result :: ("show") "show" begin
definition "show_result \<equiv> (\<lambda>x. case x of Ok x \<Rightarrow> ''Ok '' @. x | Err e \<Rightarrow> e )"
instance by standard
end

definition "digits \<equiv> ''0123456789''"

fun nat_to_str where
"nat_to_str x = (if x < 10 then [digits!x] else nat_to_str (x div 10)@nat_to_str (x mod 10))"


instantiation int ::  "show" begin
definition "show_int \<equiv> (\<lambda>x. if x < 0 then ''-'' @ nat_to_str (nat (-x)) else nat_to_str (nat x))"
instance by standard
end


instantiation nat :: "show" begin
definition "show_nat \<equiv> nat_to_str"
instance by standard
end


value "show [1,2,3,4::int]"

fun subst :: "(varName \<rightharpoonup> ctype) \<Rightarrow> vtype \<Rightarrow> ctype"  where
  "subst \<sigma> VBool = Bool"
| "subst \<sigma> (VType n as) = CType n (map (subst \<sigma>) as)"
| "subst \<sigma> (TypeVar v) = the (\<sigma> v)"

fun checkFuncType :: "(varName \<rightharpoonup> ctype) \<Rightarrow> vtype list \<Rightarrow> ctype list \<Rightarrow> vtype \<Rightarrow> ctype result"  where
  "checkFuncType \<sigma> [] [] rt = Ok (subst \<sigma> rt)"
| "checkFuncType \<sigma> (VBool#xs) (Bool#ys) rt = checkFuncType \<sigma> xs ys rt"
| "checkFuncType \<sigma> (VType n as#xs) (CType n' as'#ys) rt = (
      if n \<noteq> n' then 
        Err (''types '' @. n @. '' and '' @. n' @. '' do not match'')
      else if length as \<noteq> length as' then
        Err (''type arguments '' @. (printSep '', '' as) @. '' and '' @. (printSep '', '' as') @. '' do not match for '' @. n)
      else
        checkFuncType \<sigma> (as@xs) (as'@ys) rt
)"
| "checkFuncType \<sigma> (TypeVar v#xs) (t#ys) rt = (
      case \<sigma> v of
        None \<Rightarrow> checkFuncType (\<sigma>(v\<mapsto>t)) xs ys rt
      | Some t' \<Rightarrow> if t = t' then checkFuncType \<sigma> xs ys rt 
                   else Err (''types '' @. t @ '' and '' @. t' @. '' do not match'')
)"
| "checkFuncType \<sigma> xs ys rt = Err (''types '' @. xs @ '' and '' @. ys @ '' do not match'')"

type_synonym type_env = "varName \<rightharpoonup> ctype"

fun check_types :: "signature \<Rightarrow> type_env \<Rightarrow> s_term \<Rightarrow> ctype result" where
  "check_types \<Sigma> \<phi> (Var v) = (case \<phi> v of Some t \<Rightarrow> Ok t | None \<Rightarrow> Err (''Variable '' @. v @ '' not defined''))"
| "check_types \<Sigma> \<phi> (Apply f as) = 
      (case function_type \<Sigma> f of
         None \<Rightarrow>  Err (''Unknown function '' @. f )
       | Some (FunctionType pst rt) \<Rightarrow>
         let asto = map (check_types \<Sigma> \<phi>) as in
         if (\<forall>x\<in> set asto. is_ok x)  then checkFuncType Map.empty pst (map the_result asto) rt 
         else
          (case filter (\<lambda>x. \<not>is_ok x) asto of
           (e#_) \<Rightarrow> Err (e .@ '' // when checking args of '' @. f)))"
| "check_types \<Sigma> \<phi> (Quantifier q t v b) = 
    (case check_types \<Sigma> (\<phi>(v\<mapsto>t)) b of 
      Ok Bool \<Rightarrow> Ok Bool
    | Ok t \<Rightarrow> Err (''Quantifier should have type bool, but was '' @. t )
    | Err e \<Rightarrow> Err e)"
| "check_types \<Sigma> \<phi> (Neg b) = 
    (case check_types \<Sigma> \<phi> b of 
     Ok Bool \<Rightarrow> Ok Bool
    | Ok t \<Rightarrow> Err (''Negation should have type bool, but was '' @. t )
    | Err e \<Rightarrow> Err e)"
| "check_types \<Sigma> \<phi> (BinaryB l op r) = 
    (case (check_types \<Sigma> \<phi> l, op, check_types \<Sigma> \<phi> r) of 
      (Ok t1, Eq, Ok t2) \<Rightarrow> if t1 = t2 then Ok Bool else Err (''Equality check of incompatible types: '' @. t1 @ '' and '' @. t2)
    | (Ok Bool, _, Ok Bool) \<Rightarrow> Ok Bool
    | (Ok t1, _, Ok t2) \<Rightarrow> Err (''Wrong operator usage: '' @. t1 @ '' and '' @. t2 ) 
    | (Err e, _, _) \<Rightarrow> Err (e @  '' // in left hand side of operator'')
    | (_, _, Err e) \<Rightarrow> Err (e @  '' // in right hand side of operator''))"
| "check_types \<Sigma> \<phi> (BoolConst _) = Ok Bool"

\<comment> \<open>Example of the type checker: Theory of arrays. \<close>

definition "t_array \<equiv> TypeName ''ar''"
definition "t_int \<equiv> TypeName ''int''"
definition "f_set \<equiv> ConstName ''set''"
definition "f_get \<equiv> ConstName ''get''"
definition "f_zero \<equiv> ConstName ''0''"
definition "v_k \<equiv> VarName ''k''"
definition "v_v \<equiv> VarName ''v''"
definition "v_a \<equiv> VarName ''a''"

definition "sig \<equiv> \<lparr>
    function_type = [f_set \<mapsto> FunctionType [VType t_array [TypeVar v_k, TypeVar v_v], TypeVar v_k, TypeVar v_v] (VType t_array [TypeVar v_k, TypeVar v_v]),
                     f_get \<mapsto> FunctionType [VType t_array [TypeVar v_k, TypeVar v_v], TypeVar v_k] (TypeVar v_v),
                     f_zero \<mapsto> FunctionType [] (VType t_int [])],
    type_arity = [t_array \<mapsto> 1, t_int \<mapsto> 0]
 \<rparr>"


\<comment> \<open>get(set(a, 0, True), 0) = True\<close>
definition "example1 \<equiv> BinaryB (Apply f_get [Apply f_set [Var v_a, Apply f_zero [], BoolConst True], Apply f_zero []]) Eq (BoolConst True)" 

value "check_types sig Map.empty example1"

value "check_types sig [v_a \<mapsto> CType t_array [CType t_int [], Bool]] (Apply f_set [Var v_a, Apply f_zero [], BoolConst True])"
value "check_types sig [v_a \<mapsto> CType t_array [CType t_int [], Bool]] (Apply f_get [Apply f_set [Var v_a, Apply f_zero [], BoolConst True], Apply f_zero []])"
value "check_types sig [v_a \<mapsto> CType t_array [CType t_int [], Bool]] example1"
value "check_types sig [v_a \<mapsto> CType t_array [Bool, Bool]] example1"













lemma "check_types sig Map.empty example1 = None"
  by eval

declare check_types.simps[[simp del]]
declare checkFuncType.simps[[simp del]]











schematic_goal sig_f_get: "function_type sig f_get = ?x"
  by (simp add: sig_def f_get_def f_set_def f_zero_def)
schematic_goal sig_f_set: "function_type sig f_set = ?x"
  by (simp add: sig_def f_get_def f_set_def f_zero_def)
schematic_goal sig_f_zero: "function_type sig f_zero = ?x"
  by (simp add: sig_def f_get_def f_set_def f_zero_def)


lemma "check_types sig [v_a \<mapsto> CType t_array [CType t_int [], Bool]] example1 = Some Bool"
  apply (subst example1_def)
  apply (subst check_types.simps) 
  apply (subst check_types.simps)
  apply (subst sig_f_get)
  apply (subst option.simps)
  apply (subst functionType.simps)
  apply (subst check_types.simps) 
  apply (subst list.map)
 apply (subst check_types.simps) 

  
  apply simp
  apply (subst check_types.simps) 
  apply simp


  by eval



end


end