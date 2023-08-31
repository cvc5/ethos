(include "../theories/Strings.smt2")

; Helper method for PfRule::CONCAT_UNIFY. Returns ok if s or a prefix of its
; head is equal to s1, where the (suffix of the) head of the reverse of s is
; checked if rev is tt. Fails otherwise.
(function concat_head_or_self ((s term) (s1 term) (rev flag) (u sort)) Ok
  (ifequal s s1
    ok
    (let ss (string_rev s rev U)
    (let sh (string_head ss)
    (ifequal sh s1
      ok
      ; otherwise we may be splitting a constant, get s1 in n-ary form
      (let s1n (string_rev (string_nary_intro s1 U) rev U)
      ; it may be that s itself is a constant, in which case we must consider
      ; it as a whole, not just its head
      (ifequal (string_is_prefix s1n ss U) tt
        ok
        ; we are splitting a constant in the head of s1, notice we must reverse
        ; its characters, since they were not reversed when computing ss
        (ifequal (string_is_prefix s1n (string_rev sh rev U) U) tt
          ok
          (fail Ok))))))))
)

; Computes whether the heads of the premise (= s t) match s1 and t1 for the
; PfRule::CONCAT_UNIFY rule
(function concat_unify ((s term) (t term) (s1 term) (t1 term) (rev flag) (u sort)) Ok
  (ifequal (concat_head_or_self s s1 rev U) ok
    (ifequal (concat_head_or_self t t1 rev U) ok
      ok
      (fail Ok))
    (fail Ok)))

(declare concat_unify (! s term
                      (! t term
                      (! s1 term
                      (! t1 term
                      (! rev flag
                      (! U sort
                      (! p (holds (= s t))
                      (! p1 (holds (= (str.len s1) (str.len t1)))
                      (! r (^ (concat_unify s t s1 t1 rev U) ok)
                          (holds (= s1 t1))))))))))))

; Computes the conclusion of the PfRule::CONCAT_CSPLIT rule
(function concat_csplit ((thead term) (t term) (s term) (rev flag) (u sort)) term
  (match (string_to_flat_form t rev U)
    ((apply t1 t2)
      (ifequal (getarg f_str.++ t1) thead
        (match (string_to_flat_form s rev U)
          ((apply s1 s2)
            (let s12 (getarg f_str.++ s1)
            (match s12
              ((char n)
                (= thead
                (ifequal rev ff
                  (str.++ s12 (str.++ (skolem (skolem_suffix_rem thead (int 1))) emptystr))
                  (str.++ (skolem (skolem_prefix thead (a.- (str.len thead) (int 1)))) (str.++ s12 emptystr)))))))))
          (fail term))))
)

(declare concat_csplit 
  (! t1 term
  (! t term
  (! s term
  (! res term
  (! rev flag
  (! U sort
  (! p1 (holds (= t s))
  (! p2 (holds (not (= (str.len t1) (int 0))))
  (! r (^ (concat_csplit t1 t s rev U) res)
    (holds res)))))))))))

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

