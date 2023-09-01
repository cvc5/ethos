(include "../theories/Strings.smt2")



; For sequences, we Use a variant of the PfRule::CONCAT_CONFLICT rule where the
; justification for the clashing characters is given in the form of a
; disequality. This is due to the fact that check whether a term is value is
; not a simple syntactic check for some types.
(function concat_conflict_deq ((s term) (t term) (sc term) (tc term) (rev flag) (u sort)) Ok
  (match (strip_prefix
           (string_to_flat_form s rev U)
           (string_to_flat_form t rev U) U)
    ((pair ss ts)
      (ifequal (string_first_char_or_empty s U) sc
        (ifequal (string_first_char_or_empty t U) tc
          ok
          (fail Ok))
        (fail Ok)))))

(declare concat_conflict_deq (! s term
                             (! t term
                             (! sc term
                             (! tc term
                             (! rev flag
                             (! U sort
                             (! p (holds (= s t))
                             (! pc (holds (not (= sc tc)))
                             (! r (^ (concat_conflict_deq s t sc tc rev U) ok)
                                (holds false)))))))))))




