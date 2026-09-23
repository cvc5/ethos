theory Isabelle_Smoke
  imports EocTest_Spec
begin

abbreviation assumptions where
  "assumptions \<equiv> CArgList_cons (Term_Boolean True)
    (CArgList_cons (Term_Apply Term_Op_not (Term_Boolean True)) CArgList_nil)"

abbreviation contradiction where
  "contradiction \<equiv> CCmdList_cons
    (CCmd_step CRule_contra CArgList_nil
      (CIndexList_cons 0 (CIndexList_cons 1 CIndexList_nil))) CCmdList_nil"

lemma accepts_contradiction: "check_refutation 100 assumptions contradiction"
  by eval

lemma rejects_wrong_premises:
  "\<not> check_refutation 100 assumptions
    (CCmdList_cons (CCmd_step CRule_contra CArgList_nil
      (CIndexList_cons 0 (CIndexList_cons 0 CIndexList_nil))) CCmdList_nil)"
  by eval

lemma rejects_open_scope:
  "\<not> check_refutation 100 CArgList_nil
    (CCmdList_cons (CCmd_assume_push (Term_Boolean False)) CCmdList_nil)"
  by eval

lemma rejects_empty_proof: "\<not> check_refutation 100 CArgList_nil CCmdList_nil"
  by eval

lemma exhaustion_is_none:
  "p_checker_is_refutation_2 1 assumptions contradiction = None"
  by eval

lemma non_linear_first_case:
  "p_selection 100 (Term_Boolean True) (Term_Boolean True)
    = Some (Term_Boolean False)"
  by eval

lemma non_linear_fallthrough:
  "p_selection 100 (Term_Boolean True) (Term_Boolean False)
    = Some (Term_Boolean True)"
  by eval

lemma zero_argument_rule:
  "p_truth 100 = Some (Term_Boolean True)"
  by eval

lemma literal_pattern:
  "p_zero 100 (Term_Numeral 0) = Some (Term_Boolean True)"
  by eval

lemma literal_fallthrough:
  "p_zero 100 (Term_Numeral (-1)) = Some (Term_Boolean False)"
  by eval

lemma stuck_propagates:
  "p_selection 100 Term_Stuck (Term_Boolean False) = Some Term_Stuck"
  by eval

lemma divergence_exhausts:
  "p_diverge 100 (Term_Boolean True) = None"
  by eval

lemma unselected_branch_does_not_exhaust:
  "p_lazy 100 (Term_Boolean True) = Some (Term_Boolean True)"
  by eval

lemma scope_pop:
  "p_invoke_cmd_list 100 CState_nil
    (CCmdList_cons (CCmd_assume_push (Term_Boolean True))
      (CCmdList_cons (CCmd_step CRule_truth CArgList_nil CIndexList_nil)
        (CCmdList_cons (CCmd_step_pop CRule_scope CArgList_nil
          (CIndexList_cons 0 CIndexList_nil)) CCmdList_nil)))
   = Some (CState_cons (CStateObj_proven
       (Term_Apply (Term_Apply Term_Op_implies (Term_Boolean True))
         (Term_Boolean True))) CState_nil)"
  by eval

lemma distinct_names:
  "p_distinct_names 100 Term_Op_a_b = Some Term_Op_Boolean"
  by eval

lemma escaped_name_and_stuck:
  "p_distinct_names 100 Term_Op_a_x2db = Some Term_Op_Stuck
    \<and> Term_Op_Stuck \<noteq> Term_Stuck"
  by eval

lemma readable_name_collisions:
  "p_distinct_names 100 Term_Op_a_b_2 = Some (Term_Boolean True)
   \<and> p_distinct_names 100 Term_Op_a_b_3 = Some Term_Op_a_b
   \<and> p_distinct_names 100 Term_Op_a_b_2_2 = Some Term_Op_a_x2db
   \<and> p_distinct_names 100 Term_Op_eq_2 = Some Term_Op_eq_2
   \<and> Term_Op_eq \<noteq> Term_Op_eq_2
   \<and> p_operator_names 100 (Term_Boolean True)
      = Some (Term_Apply (Term_Apply Term_Op_eq (Term_Boolean True)) (Term_Boolean True))
   \<and> p_distinct_names 100 Term_Op_a_x20b = Some Term_Op_Boolean
   \<and> p_distinct_names 100 Term_Op_a_x20b_2 = Some Term_Op_Stuck"
  by eval

lemma readable_rule_collisions:
  "p_arith_elim_int_gt 100 = Some (Term_Boolean True)
   \<and> p_arith_elim_int_gt_2 100 = Some (Term_Boolean False)
   \<and> p_arith_elim_int_gt_2_2 100 = Some Term_Op_Boolean
   \<and> p_checker_is_refutation 100 = Some (Term_Boolean True)"
  by eval

lemma readable_parameter_collisions:
  "p_parameter_names 100 (Term_Boolean True) (Term_Boolean False)
      = Some (Term_Boolean False)
   \<and> p_parameter_names 100 (Term_Boolean False) (Term_Boolean True)
      = Some (Term_Boolean False)"
  by eval

lemma indexed_operator:
  "p_indexed_rule 100
      (Term_UOp1 UserOp1_Op_indexed (Term_Numeral 0)) = Some (Term_Boolean True)
   \<and> p_indexed_rule 100
      (Term_UOp1 UserOp1_Op_indexed (Term_Numeral 1)) = Some (Term_Boolean False)"
  by eval

lemma powers_and_logarithms:
  "p_pow 100 (Term_Numeral 3) (Term_Numeral 4) = Some (Term_Numeral 81)
   \<and> p_pow 100 (Term_Rational (3 / 2)) (Term_Numeral 2)
      = Some (Term_Rational (9 / 4))
   \<and> p_pow 100 (Term_Numeral 3) (Term_Numeral (-1)) = Some (Term_Numeral 0)
   \<and> p_log 100 (Term_Numeral 2) (Term_Numeral 1025) = Some (Term_Numeral 10)
   \<and> p_log 100 (Term_Numeral 1) (Term_Numeral 10) = Some (Term_Numeral 0)"
  by eval

lemma rational_floor_and_unicode:
  "p_to_z 100 (Term_Rational (-3 / 2)) = Some (Term_Numeral (-2))
   \<and> p_to_z 100 (Term_String [128512]) = Some (Term_Numeral 128512)
   \<and> p_to_str 100 (Term_Numeral 128512) = Some (Term_String [128512])
   \<and> p_to_str 100 (Term_Numeral 196608) = Some Term_Stuck"
  by eval

lemma string_operations:
  "p_extract 100 (Term_String [97, 98, 99]) (Term_Numeral 1) (Term_Numeral 2)
      = Some (Term_String [98, 99])
   \<and> p_extract 100 (Term_String [97]) (Term_Numeral (-1)) (Term_Numeral 2)
      = Some (Term_String [])
   \<and> p_find 100 (Term_String [97, 98, 99]) (Term_String [98, 99])
      = Some (Term_Numeral 1)
   \<and> eoc_str_indexof [97] [] 1 = 1
   \<and> eoc_str_indexof [97] [] 2 = -1
   \<and> eoc_str_indexof [97] [98] 0 = -1"
  by eval

lemma binary_operations:
  "p_or 100 (Term_Binary 3 5) (Term_Binary 3 2) = Some (Term_Binary 3 7)
   \<and> p_xor 100 (Term_Binary 3 5) (Term_Binary 3 3) = Some (Term_Binary 3 6)
   \<and> p_not 100 (Term_Binary 3 5) = Some (Term_Binary 3 2)
   \<and> p_extract 100 (Term_Binary 4 13) (Term_Numeral 1) (Term_Numeral 2)
      = Some (Term_Binary 2 2)
   \<and> p_concat 100 (Term_Binary 3 5) (Term_Binary 2 2)
      = Some (Term_Binary 5 22)"
  by eval

lemma structural_comparison:
  "p_cmp 100 (Term_Numeral 1) (Term_Numeral 2) = Some (Term_Boolean True)
   \<and> p_cmp 100 (Term_Numeral 2) (Term_Numeral 1) = Some (Term_Boolean False)
   \<and> p_cmp 100 (Term_String [97]) (Term_String [97]) = Some (Term_Boolean False)
   \<and> key_Term (Term_String [0, 1]) \<noteq> key_Term (Term_String [1, 0])"
  by eval

lemma mutual_recursion:
  "p_mutual_rule 100 (Term_Numeral 4) = Some (Term_Boolean True)
   \<and> p_mutual_rule 100 (Term_Numeral 3) = Some (Term_Boolean False)
   \<and> p_mutual_rule 2 (Term_Numeral 4) = None"
  by eval

end
