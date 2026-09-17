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
    (CCmdList_cons (CCmd_assume_x5fpush (Term_Boolean False)) CCmdList_nil)"
  by eval

lemma rejects_empty_proof: "\<not> check_refutation 100 CArgList_nil CCmdList_nil"
  by eval

lemma exhaustion_is_none:
  "p__x24eo_x5fchecker_x5fis_x5frefutation 1 assumptions contradiction = None"
  by eval

lemma non_linear_first_case:
  "p__x24eo_x5fprog_x5fselection 100 (Term_Boolean True) (Term_Boolean True)
    = Some (Term_Boolean False)"
  by eval

lemma non_linear_fallthrough:
  "p__x24eo_x5fprog_x5fselection 100 (Term_Boolean True) (Term_Boolean False)
    = Some (Term_Boolean True)"
  by eval

lemma zero_argument_rule:
  "p__x24eo_x5fprog_x5ftruth 100 = Some (Term_Boolean True)"
  by eval

lemma literal_pattern:
  "p__x24eo_x5fprog_x5fzero 100 (Term_Numeral 0) = Some (Term_Boolean True)"
  by eval

lemma literal_fallthrough:
  "p__x24eo_x5fprog_x5fzero 100 (Term_Numeral (-1)) = Some (Term_Boolean False)"
  by eval

lemma stuck_propagates:
  "p__x24eo_x5fprog_x5fselection 100 Term_Stuck (Term_Boolean False) = Some Term_Stuck"
  by eval

lemma divergence_exhausts:
  "p__x24eo_x5fprog_x5fdiverge 100 (Term_Boolean True) = None"
  by eval

lemma unselected_branch_does_not_exhaust:
  "p__x24eo_x5fprog_x5flazy 100 (Term_Boolean True) = Some (Term_Boolean True)"
  by eval

lemma scope_pop:
  "p__x24eo_x5finvoke_x5fcmd_x5flist 100 CState_nil
    (CCmdList_cons (CCmd_assume_x5fpush (Term_Boolean True))
      (CCmdList_cons (CCmd_step CRule_truth CArgList_nil CIndexList_nil)
        (CCmdList_cons (CCmd_step_x5fpop CRule_scope CArgList_nil
          (CIndexList_cons 0 CIndexList_nil)) CCmdList_nil)))
   = Some (CState_cons (CStateObj_proven
       (Term_Apply (Term_Apply Term_Op__x3d_x3e (Term_Boolean True))
         (Term_Boolean True))) CState_nil)"
  by eval

lemma distinct_names:
  "p__x24eo_x5fprog_x5fdistinct_x5fnames 100 Term_Op_a_x2db = Some Term_Op_Boolean"
  by eval

lemma escaped_name_and_stuck:
  "p__x24eo_x5fprog_x5fdistinct_x5fnames 100 Term_Op_a_x5fx2db = Some Term_Op_Stuck
    \<and> Term_Op_Stuck \<noteq> Term_Stuck"
  by eval

end
