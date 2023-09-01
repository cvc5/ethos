(include "../theories/Strings.smt2")



; Checks whether the conditions on the premise (= s t) is satisfied for the
; PfRule::CONCAT_CONFLICT rule
(function concat_conflict ((s term) (t term) (rev flag) (u sort)) Ok
  (match (strip_prefix
           (string_to_flat_form s rev U)
           (string_to_flat_form t rev U) U)
    ((pair ss ts)
      (ifequal
        (string_first_char_or_empty ss U)
        (string_first_char_or_empty ts U)
        (fail Ok)
        ok))))

(declare concat_conflict (! s term
                         (! t term
                         (! rev flag
                         (! U sort
                         (! p (holds (= s t))
                         (! r (^ (concat_conflict s t rev U) ok)
                            (holds false))))))))

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


; Computes the conclusion of PfRule::RE_UNFOLD_POS
(function re_unfold_pos ((t term) (r term)) term
  (match r
    ((apply r1 r2)
      (match r1
        ; case for star
        (f_re.*
          (let rr (re.++ r2 (re.++ r (re.++ r2 re.empty)))
          (match (re_unfold_pos_concat t rr rr 0)
            ((pair p1 p2)
              (or (= t emptystr)
                (or (str.in_re t r2)
                  (or (and (string_nary_elim (and (= t p1) p2) String) (non_empty_concats p1 String))
                    false)))))))
        ((apply r11 r12)
          (match r11
            ; case for concatenation
            (f_re.++
              (match (re_unfold_pos_concat t r r 0)
                ((pair p1 p2) (string_nary_elim (and (= t p1) p2) String))))
))))))

(declare re_unfold_pos (! t term (! r term (! s term (! f (holds (str.in_re t r)) (! U (^ (re_unfold_pos t r) s) (holds s)))))))

