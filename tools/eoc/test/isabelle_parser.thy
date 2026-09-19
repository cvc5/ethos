theory Isabelle_Parser
  imports EocTest_Checker "HOL-Library.Code_Target_Numeral"
begin

definition runtime_nat :: "integer \<Rightarrow> nat" where
  "runtime_nat n = nat_of_integer n"

definition runtime_int :: "integer \<Rightarrow> int" where
  "runtime_int n = int_of_integer n"

definition runtime_rational :: "integer \<Rightarrow> integer \<Rightarrow> Term" where
  "runtime_rational n d = Term_Rational
    (of_int (int_of_integer n) / of_int (int_of_integer d))"

export_code open check_refutation p_typeof p_nil
  runtime_nat runtime_int runtime_rational
  in SML module_name CPC file_prefix cpc

end
