section "Show Typeclass"

theory show_typeclass
imports Main
begin

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

instantiation option :: ("show") "show" begin
definition "show_option \<equiv> (\<lambda>x. case x of Some x \<Rightarrow> ''Some '' @. x | None \<Rightarrow> ''None'' )"
instance by standard
end

end