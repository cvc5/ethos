theory $EO_CALC$_Model
  imports "$EO_CALC$.$EO_CALC$_Checker"
begin

text \<open>
  Generated from model-smt's EO definitions. These logical definitions are
  separate from the executable checker and do not take a recursion budget.
\<close>

$DATATYPES$

fun eoc_model_decimal :: "nat => nat list" where
  "eoc_model_decimal n = (if n < 10 then [48 + n]
    else eoc_model_decimal (n div 10) @ [48 + n mod 10])"

$PROGRAMS$

end
