theory Isabelle_Model
  imports EocModel_Model
begin

lemma boolean_translation:
  "m_to_smt (Term_Boolean b) = SmtTerm_Boolean b"
  by simp

lemma negation_translation:
  "m_to_smt (Term_Apply Term_Op_not t) = SmtTerm_not (m_to_smt t)"
  by simp

lemma conjunction_translation:
  "m_to_smt (Term_Apply (Term_Apply Term_Op_and s) t) =
    SmtTerm_and (m_to_smt s) (m_to_smt t)"
  by simp

lemma boolean_model_contradiction:
  "m_smtx_model_eval_and (SmtValue_Boolean b)
    (m_smtx_model_eval_not (SmtValue_Boolean b)) = SmtValue_Boolean False"
  by simp

lemma failed_values_are_not_truth:
  "m_smtx_model_eval_not SmtValue_NotValue = SmtValue_NotValue"
  by simp

text \<open>A successful execution of the unchanged checker rule produces
  precisely the translated Boolean false, at every sufficient checker fuel.
  This is a translation contract, not yet a full semantic soundness theorem.\<close>

lemma contra_translated_result:
  assumes "p_contra fuel (Proof_pf F)
    (Proof_pf (Term_Apply Term_Op_not F)) = Some result"
  shows "m_to_smt result = SmtTerm_Boolean False"
  using assms by (cases fuel) auto

lemma variable_translation:
  "m_to_smt (Term_Var (Term_String s) Term_Bool) = SmtTerm_Var s SmtType_Bool"
  by simp

lemma uninterpreted_constant_names:
  "m_to_smt (Term_UConst 123 Term_Bool) =
    SmtTerm_UConst [64, 117, 46, 49, 50, 51] SmtType_Bool"
  by eval

lemma datatype_translation:
  "m_to_smt_type (Term_DatatypeType [76]
    (DatatypeDecl_cons [76]
      (Datatype_sum (DatatypeCons_cons Term_Bool DatatypeCons_unit) Datatype_null)
      DatatypeDecl_nil)) =
   SmtType_Datatype [76]
    (SmtDatatypeDecl_cons [76]
      (SmtDatatype_sum (SmtDatatypeCons_cons SmtType_Bool SmtDatatypeCons_unit)
        SmtDatatype_null) SmtDatatypeDecl_nil)"
  by (simp add: m_to_smt_reserved_datatype_name.simps)

lemma checker_still_rejects_zero_budget:
  "\<not> check_refutation 0 assumptions commands"
  by simp

export_code check_refutation in SML module_name EocChecker file_prefix checker_after

end
