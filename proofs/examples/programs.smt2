; Tests for the gerneral programs.

(include "../theories/Core.smt2")

; Proof rule to test if the parameter `test` evaluates to `reference`
(declare-rule is_equals ((T Type) (test T) (reference T))
    :args (test reference)
    :requires ((test reference))
    :conclusion true
)

(include "../programs/Nary.smt2")

(declare-const c1 Bool)
(declare-const c2 Bool)
(declare-const c3 Bool)

; Test removeRight
(step rr1 :rule is_equals :premises () :args ((removeRight c1 (or c2 c1)) c2))
(step rr2 :rule is_equals :premises () :args ((removeRight c1 (or c1 c2)) c2))
(step rr3 :rule is_equals :premises () :args ((removeRight c1 (or c1 (or c2 c3))) (or c2 c3)))
(step rr4 :rule is_equals :premises () :args ((removeRight c1 (or c2 (or c1 c3))) (or c2 c3)))
(step rr5 :rule is_equals :premises () :args ((removeRight c1 (or c2 (or c3 c2))) (or c2 c3)))

; Test appendRight
(step ar1 :rule is_equals :premises () :args ((appendRight or c1 c2) (or c1 c2)))
(step ar2 :rule is_equals :premises () :args ((appendRight or c3 (or c1 c2))         (or c1 (or c2 c3))))
(step ar3 :rule is_equals :premises () :args ((appendRight or c3 (or (or c1 c1) c2)) (or (or c1 c1) (or c2 c3))))
(step ar4 :rule is_equals :premises () :args ((appendRight or c3 (or c1 (or c1 c2))) (or c1 (or c1 (or c2 c3)))))

; Test removeLeft
(step rl1 :rule is_equals :premises () :args ((removeLeft c1 (or c2 c1)) c2))
(step rl2 :rule is_equals :premises () :args ((removeLeft c1 (or c1 c2)) c2))
(step rl3 :rule is_equals :premises () :args ((removeLeft c1 (or (or c1 c2) c3)) (or c2 c3)))
(step rl4 :rule is_equals :premises () :args ((removeLeft c1 (or (or c2 c1) c3)) (or c2 c3)))
(step rl5 :rule is_equals :premises () :args ((removeLeft c1 (or (or c2 c3) c2)) (or c2 c3)))

; Test appendLeft
(step al1 :rule is_equals :premises () :args ((appendLeft or c1 c2) (or c1 c2)))
(step al2 :rule is_equals :premises () :args ((appendLeft or c3 (or c1 c2)        ) (or (or c3 c1) c2)))
(step al3 :rule is_equals :premises () :args ((appendLeft or c3 (or (or c1 c1) c2)) (or (or (or c3 c1) c1) c2)))
(step al4 :rule is_equals :premises () :args ((appendLeft or c3 (or c1 (or c1 c2))) (or (or c3 (or c1 c1)) c2)))

