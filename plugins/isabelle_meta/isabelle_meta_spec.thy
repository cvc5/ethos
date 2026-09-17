theory $EO_CALC$_Spec
  imports $EO_CALC$_Checker
begin

text \<open>
  Initial proof scaffolding for iogos. The interpretation of terms and the
  premises under which each obligation holds belong to the importing theory.
  These definitions do not assert soundness of the generated checker.
\<close>

$OBLIGATIONS$

definition checker_sound_for where
  "checker_sound_for unsatisfiable =
    (\<forall>fuel assumptions commands.
      check_refutation fuel assumptions commands \<longrightarrow>
      unsatisfiable assumptions)"

lemma checked_refutation:
  assumes "checker_sound_for unsatisfiable"
      and "check_refutation fuel assumptions commands"
  shows "unsatisfiable assumptions"
  using assms unfolding checker_sound_for_def by blast

end
