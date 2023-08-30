(include "../theories/Arith.smt2")

(program arith.eval ((T Type) (U Type) (S Type) (a T) (b U) (z S))
    (S) S
    (
      ((arith.eval (= a b))  (alf.is_eq (arith.eval a) (arith.eval b)))
      ((arith.eval (< a b))  (alf.is_neg (arith.eval (- a b))))
      ((arith.eval (<= a b)) (let ((x (arith.eval (- a b))))
                                 (alf.or (alf.is_neg x) (alf.is_zero x))))
      ((arith.eval (+ a b))  (alf.add (arith.eval a) (arith.eval b)))
      ((arith.eval (- a b))  (alf.add (arith.eval a) (alf.neg (arith.eval b))))
      ((arith.eval z)        z)
    )
)

(program arith_rel_sum ((T Type) (U Type) (S Type) (r1 T) (r2 U))
  (T U) S
  (
    ((arith_rel_sum < <) <)
    ((arith_rel_sum < =) <)
    ((arith_rel_sum < <=) <)
    ((arith_rel_sum <= <) <)
    ((arith_rel_sum <= =) <=)
    ((arith_rel_sum <= <=) <=)
    ((arith_rel_sum = <) <)
    ((arith_rel_sum = =) =)
    ((arith_rel_sum = <=) <=)
  )
)

(program arith_rel_inv ((T Type) (U Type) (S Type))
  (T) S
  (
    ((arith_rel_inv =) =)
    ((arith_rel_inv <) >)
    ((arith_rel_inv <=) >=)
    ((arith_rel_inv >) <)
    ((arith_rel_inv >=) <=)
  )
)

(program arith_rel_neg ((T Type) (U Type) (S Type))
  (T) S
  (
    ((arith_rel_neg <) >=)
    ((arith_rel_neg <=) >)
    ((arith_rel_neg >) <=)
    ((arith_rel_neg >=) <)
  )
)

(program arith_rel_trichotomy ((T Type) (U Type) (S Type))
  (T U) S
  (
    ((arith_rel_trichotomy = <) >)
    ((arith_rel_trichotomy = >) <)
    ((arith_rel_trichotomy > =) <)
    ((arith_rel_trichotomy < =) >)
    ((arith_rel_trichotomy > <) =)
    ((arith_rel_trichotomy < >) =)
  )
)

;
(program arith_normalize_lit ((T Type) (U Type) (r (-> T U Bool)) (a T) (b U))
  (Bool) Bool
  (
    ((arith_normalize_lit (not (r a b))) (_ (arith_rel_neg r) a b))
    ((arith_normalize_lit (r a b)) (r a b))
  )
)
