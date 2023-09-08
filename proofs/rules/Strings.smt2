(include "../theories/Strings.smt2")
(include "../programs/Strings.smt2")


;;;;;;;;;; Core

(declare-rule string_length_pos ((U Type) (s U))
  :args (U s)
  :conclusion
    (or (and (= (str.len s) 0) (= s (mk_emptystr U))) (> (str.len s) 0))
)

(declare-rule string_length_non_empty ((U Type) (s Type) (t Type))
  :premises ((not (= s t)))
  :requires (((string_is_empty t) true))
  :conclusion (not (= (str.len s) 0))
)

; the PfRule::CONCAT_EQ rule
(declare-rule concat_eq ((U Type) (s U) (t U) (rev Bool))
  :premises ((= s t))
  :args (U rev)
  :conclusion
    (alf.match ((ss U) (ts U))
      (strip_prefix
           (string_to_flat_form U s rev) 
           (string_to_flat_form U t rev))
      ((@pair ss ts)
        (= 
          (string_from_flat_form U ss rev)
          (string_from_flat_form U ts rev))))
)


; returns true if s1 is a prefix of s, taking into account flattening
(define string_is_prefix ((U Type) (s U) (s1 U) (rev Bool))
  (let ((sf (string_to_flat_form U s rev)))
  (let ((sf1 (string_to_flat_form U s1 rev)))
  (nary.is_prefix str.++ alf.nil sf1 sf))))

(declare-rule concat_unify ((U Type) (s U) (t U) (s1 U) (t1 U) (rev Bool))
  :premises ((= s t) (= (str.len s1) (str.len t1)))
  :args (U rev)
  :requires (((string_is_prefix U s s1 rev) true) ((string_is_prefix U t t1 rev) true))
  :conclusion (= s1 t1))

(declare-rule concat_csplit ((U Type) (t U) (s U) (u U) (rev Bool))
  :premises ((= t s) (not (= (str.len u) 0)))
  :args (U rev)
  :conclusion
    (alf.match ((t1 U) (t2 U :list))
      (string_to_flat_form U t rev)
      ((str.++ t1 t2)
        (alf.requires t1 u
          (alf.match ((s1 U) (s2 U :list))
            (string_to_flat_form U s rev)
            ((str.++ s1 s2)
              (alf.requires (check_length_one s1) true    ; checks if char
                (= u
                  (alf.ite rev
                    (str.++ (skolem (skolem_prefix U u (- (str.len u) 1))) s1)
                    (str.++ s1 (skolem (skolem_suffix_rem U u 1)))))))))))
)

; the PfRule::CONCAT_CONFLICT rule, for strings only
(declare-rule concat_conflict ((s String) (t String) (rev Bool))
  :premises ((= s t))
  :args (rev)
  :conclusion
    ; strip the prefix of the equality
    (alf.match ((ss String) (ts String))
      (strip_prefix
           (string_to_flat_form String s rev)
           (string_to_flat_form String t rev))
      ((@pair ss ts)
          ; ensure the LHS is char or empty
          (let ((cs (string_first_char_or_empty ss)))
          (alf.ite (alf.is_eq cs alf.fail) alf.fail
            ; ensure the RHS is char or empty
            (let ((ct (string_first_char_or_empty ts)))
            (alf.ite (alf.is_eq ct alf.fail) alf.fail
              ; ensure they are disequal, return false
              (alf.requires (alf.is_eq cs ct) false false)))))
          ))
)
; the PfRule::CONCAT_CONFLICT_DEQ rule, for sequences only
(declare-rule concat_conflict_deq ((U Type) (s (Seq U)) (t (Seq U)) (x U) (y U) (rev Bool))
  :premises ((= s t) (not (= x y)))
  :args (rev (Seq U))
  :conclusion
    ; strip the prefix of the equality
    (alf.match ((ss (Seq U)) (ts (Seq U)))
      (strip_prefix
           (string_to_flat_form (Seq U) s rev)
           (string_to_flat_form (Seq U) t rev))
      ((@pair ss ts)
          ; take the first character from each side, should give x and y
          (alf.requires (string_first_char_or_empty ss) x
          (alf.requires (string_first_char_or_empty ts) y
              false))))
)

;;;;;;;;;; Regular expressions


(declare-rule re_inter ((x String) (s RegLan) (t RegLan))
  :premises ((str.in_re x s) (str.in_re x t))
  :conclusion (str.in_re x (re.inter s t))
)

(declare-rule re_unfold_pos ((t String) (r RegLan))
  :premises ((str.in_re t r))
  :conclusion
    (alf.match ((r1 RegLan) (r2 RegLan :list))
      r
      ((re.* r1)
        (alf.match ((k1 String) (k2 String) (k3 String) (M Bool :list))
          (re_unfold_pos_concat t (re.++ r1 r r1))
          ((@pair (str.++ k1 k2 k3) M)
             (or 
               (= t "") 
               (str.in_re t r1)
               (and
                  (alf.cons and (= t (str.++ k1 k2 k3)) M)
                  (not (= k1 ""))
                  (not (= k3 "")))))))
      ((re.++ r1 r2)
        (alf.match ((tk String) (M Bool :list))
          (re_unfold_pos_concat t r)
          ((@pair tk M)
             (alf.from_list and (and (= t tk) M)))))))

;;;;;;;;;; Extended functions 

(declare-rule string_reduction ((U Type) (s U))
  :args (U s)
  :conclusion (and (string_reduction_pred s U) (= s (skolem s)))
)

(declare-rule string_eager_reduction ((U Type) (s U))
  :args (U s)
  :conclusion (mk_string_eager_reduction s U)
)
