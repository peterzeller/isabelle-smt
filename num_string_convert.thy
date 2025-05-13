theory num_string_convert
  imports Main
begin

section "Number and string conversions"

definition digit_to_char :: "nat \<Rightarrow> char" where
  "digit_to_char d \<equiv> char_of_integer (integer_of_nat (d + 48))"

definition char_to_digit :: "char \<Rightarrow> nat" where
  "char_to_digit c \<equiv> nat_of_integer (integer_of_char c) - 48"

fun nat_to_string :: "nat \<Rightarrow> string" where
  "nat_to_string i = (if i < 10 then [digit_to_char i] 
                    else nat_to_string (i div 10) @ [digit_to_char (i mod 10)])"

lemma nat_to_string_example: "nat_to_string 123 = ''123''"
  by eval

fun string_to_nat_r :: "string \<Rightarrow> nat" where
  "string_to_nat_r [] = 0"
| "string_to_nat_r (x#xs) = char_to_digit x + 10 * string_to_nat_r xs"

definition "string_to_nat s \<equiv> string_to_nat_r (rev s)"

lemma string_to_nat_example: "string_to_nat ''123'' = 123"
  by eval

lemma char_to_digit_bij:
  assumes "d < 10"
  shows "char_to_digit (digit_to_char d) = d"
proof (auto simp add: char_to_digit_def digit_to_char_def char_of_integer_def integer_of_char_def)

  have "d + 48 < 10 + 48"
    using assms by auto


  hence "d + 48 < 58"
    by auto


  hence "integer_of_nat (d + 48) < 58"
    by (metis integer_of_nat_eq_of_nat of_nat_less_iff of_nat_numeral)


  hence "integer_of_nat (d + 48) < 256"
    by auto


  have "(integer_of_nat (d + 48) mod 256) = integer_of_nat d + 48"
    by (metis \<open>integer_of_nat (d + 48) < 256\<close> integer_of_nat_eq_of_nat of_nat_0_le_iff of_nat_add of_nat_numeral unique_euclidean_semiring_numeral_class.mod_less)


  show "nat_of_integer (integer_of_nat (d + 48) mod 256) - 48 = d"
    by (metis \<open>integer_of_nat (d + 48) mod 256 = integer_of_nat d + 48\<close> add_diff_cancel_right' integer_of_nat_eq_of_nat nat_of_integer_integer_of_nat of_nat_add of_nat_numeral)

qed

lemma string_to_nat_bij:
  "string_to_nat (nat_to_string n) = n"
proof (induct n rule: less_induct)
  case (less x)
  show ?case
  proof (cases "x < 10")
    case True
    then show ?thesis 
      by (auto simp add: string_to_nat_def char_to_digit_bij)
  next
    case False

    show ?thesis
    proof (subst nat_to_string.simps, simp add: False del: nat_to_string.simps)

      have IH: "string_to_nat (nat_to_string (x div 10)) = x div 10"
        using False less.hyps by auto


      have "string_to_nat (nat_to_string (x div 10) @ [digit_to_char (x mod 10)])
       = char_to_digit (digit_to_char (x mod 10)) + 10 * string_to_nat (nat_to_string (x div 10))"
        by (subst string_to_nat_def,
            simp del: nat_to_string.simps,
            fold string_to_nat_def,
            simp)
      also have "... = char_to_digit (digit_to_char (x mod 10)) + 10 * (x div 10)"
        using IH by simp
      also have "... = (x mod 10) + 10 * (x div 10)"
        by (simp add: char_to_digit_bij)
      also have "... = x"
        using mod_mult_div_eq by blast

      finally
      show "string_to_nat (nat_to_string (x div 10) @ [digit_to_char (x mod 10)]) = x"
        by simp
    qed
  qed
qed

definition "is_digit d \<equiv> d\<in>set ''0123456789''"

definition is_nat_string :: "string \<Rightarrow> bool" where
  "is_nat_string s \<equiv> case s of 
    [] \<Rightarrow> False
   | [d] \<Rightarrow> is_digit d
   | (d#ds) \<Rightarrow> d \<noteq> CHR ''0'' \<and> (\<forall>c\<in>set s. is_digit c)"



end