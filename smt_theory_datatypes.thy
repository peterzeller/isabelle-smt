section "The Theory of Datatyps"

theory smt_theory_datatypes
  imports smt_theories
begin

datatype datatype_def = 
  DatatypeDef (dt_name:typeName) (dt_typeVars:"varName list") (dt_cases:"(constName \<times> (constName \<times> vtype) list) list")

definition "discriminatorName c  \<equiv> (ConstName (''is_'' @constName_name c))"

find_consts name: map "'b \<Rightarrow> 'a list"

definition "example_dts \<equiv> [
DatatypeDef (TypeName ''list'') [VarName ''a''] [
    (ConstName ''Nil'', []), 
     (ConstName ''Cons'', [
          (ConstName ''head'', TypeVar (VarName ''a'')),
          (ConstName ''tail'', VType (TypeName ''list'') [TypeVar (VarName ''a'')])] )]
]"


definition dt_constructors where
"dt_constructors dts \<equiv> 
  List.maps (\<lambda>dt. 
    List.maps (\<lambda>(c,args). 
      [(c, FunctionType (map snd args) (VType (dt_name dt) (map TypeVar (dt_typeVars dt))))]) 
    (dt_cases dt))
   dts    
 "

value "dt_constructors example_dts"


definition dt_sig :: "datatype_def list \<Rightarrow> signature" where
"dt_sig dts \<equiv> \<lparr>
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

definition dt_theory :: "datatype_def list \<Rightarrow>  'u::universe smt_theory" where
"int_theory dts \<equiv> \<lparr>
  t_signature = dt_sig dts,
  t_models = Collect (is_dt_model dts)
\<rparr>"


end