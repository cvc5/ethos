(include "../theories/Strings.smt2")
(include "../programs/Strings.smt2")


(declare-rule string_length_non_empty ((U Type) (s Type) (t Type))
  :premises ((not (= s t)))
  :requires (((string_is_empty t) true))
  :conclusion (not (= (str.len s) 0))
)

; the PfRule::CONCAT_EQ rule
(declare-rule concat_eq ((U Type) (s U) (t U) (rev Bool))
  :premises ((= s t))
  :args (rev U)
  :conclusion
    (alf.match ((ss U) (ts U))
      (strip_prefix
           (string_to_flat_form U s rev) 
           (string_to_flat_form U t rev) U)
      ((pair ss ts)
        (= 
          (string_from_flat_form U ss rev)
          (string_from_flat_form U ts rev))))
)



(declare-rule string_length_pos ((U Type) (s U))
  :args (U s)
  :conclusion
    (or (and (= (str.len s) 0) (= s (mk_emptystr U))) (> (str.len s) 0))
)

(declare-rule re_inter ((x String) (s RegLan) (t RegLan))
  :premises ((str.in_re x s) (str.in_re x t))
  :conclusion (str.in_re (re.inter s t))
)

(declare-rule string_reduction ((U Type) (s U))
  :args (U s)
  :conclusion (and (string_reduction_pred s U) (= s (skolem s)))
)

(declare-rule string_eager_reduction ((U Type) (s U))
  :args (U s)
  :conclusion (mk_string_eager_reduction s U)
)
