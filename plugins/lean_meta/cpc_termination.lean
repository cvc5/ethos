-- Termination clauses for the programs of the CPC signature.
--
-- This is the file --lean-config names when the input is CPC; the format and
-- what the clauses are for are described in plugins/lean_meta/termination.lean,
-- which holds the ones for the deep embedding itself.

-- Distinctness of a list of values is decided by walking the list and, at each
-- element, the rest of it, so the measure is the size of the two lists.

-- $set_is_not_subset $seq_distinct_terms
termination_by x1 x2 x3 => sizeOf x1 + sizeOf x2

-- $dt_distinct_terms
termination_by x1 x2 => sizeOf x1 + sizeOf x2

-- $are_distinct_terms_type
termination_by x1 x2 x3 => sizeOf x1 + sizeOf x2 + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

-- Flattening a regular expression alternates between the tree and a pass over
-- it, which the flag distinguishes, so the measure counts the tree twice and
-- breaks the tie with the flag.

-- $re_flatten
termination_by flag tree => 2 * sizeOf tree + (if flag = Term.Boolean true then 1 else 0)
decreasing_by
  all_goals simp_wf
  all_goals omega

-- Regular expression inclusion descends through four mutually recursive
-- helpers, so each step is given room by scaling the measure, and the base
-- case is ordered after the others by the offset.

-- $str_re_includes_lhs_union $str_re_includes_lhs_star $str_re_includes_rhs_inter $str_re_includes_rec
termination_by a b => 4 * (sizeOf a + sizeOf b)
decreasing_by
  all_goals simp_wf
  all_goals omega

-- $str_re_includes_base_rec
termination_by a b => 4 * (sizeOf a + sizeOf b) + 1
decreasing_by
  all_goals simp_wf
  all_goals omega
