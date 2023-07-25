; Tests for the gerneral programs.

(include "../theories/Core.smt2")
(include "../programs/Nary.smt2")

(declare-const c1 Bool)
(declare-const c2 Bool)
(declare-const c3 Bool)

; Test removeRight
(declare-rule check_removeRight((x Bool) (in Bool) (out Bool))
    :args (x in out)
    :requires (((removeRight x in) out))
    :conclusion true
)
(step rr1 :rule check_removeRight :args (c1 (or c2 c1)         c2))
(step rr2 :rule check_removeRight :args (c1 (or c1 c2)         c2))
(step rr3 :rule check_removeRight :args (c1 (or c1 (or c2 c3)) (or c2 c3)))
(step rr4 :rule check_removeRight :args (c1 (or c2 (or c1 c3)) (or c2 c3)))
(step rr5 :rule check_removeRight :args (c1 (or c2 (or c3 c2)) (or c2 (or c3 c2))))

; Test appendRight
(declare-rule check_appendRight((t1 Bool) (t2 Bool) (out Bool))
    :args (t1 t2 out)
    :requires (((appendRight or t1 t2) out))
    :conclusion true
)
(step ar1 :rule check_appendRight :args (c1 c2                 (or c1 c2)))
(step ar2 :rule check_appendRight :args (c3 (or c1 c2)         (or c3 (or c1 c2))))
(step ar3 :rule check_appendRight :args (c3 (or (or c1 c1) c2) (or c3 (or (or c1 c1) c2))))
(step ar4 :rule check_appendRight :args (c3 (or c1 (or c1 c2)) (or c3 (or c1 (or c1 c2)))))
(step ar5 :rule check_appendRight :args ((or c1 c2)         c3 (or c1 (or c2 c3))))
(step ar6 :rule check_appendRight :args ((or (or c1 c1) c2) c3 (or (or c1 c1) (or c2 c3))))
(step ar7 :rule check_appendRight :args ((or c1 (or c1 c2)) c3 (or c1 (or c1 (or c2 c3)))))

; Test removeLeft
(declare-rule check_removeLeft((x Bool) (in Bool) (out Bool))
    :args (x in out)
    :requires (((removeLeft x in) out))
    :conclusion true
)
(step rl1 :rule check_removeLeft :args (c1 (or c2 c1)         c2))
(step rl2 :rule check_removeLeft :args (c1 (or c1 c2)         c2))
(step rl3 :rule check_removeLeft :args (c1 (or (or c1 c2) c3) (or c2 c3)))
(step rl4 :rule check_removeLeft :args (c1 (or (or c2 c1) c3) (or c2 c3)))
(step rl5 :rule check_removeLeft :args (c1 (or (or c2 c3) c2) (or (or c2 c3) c2)))

; Test appendLeft
(declare-rule check_appendLeft((t1 Bool) (t2 Bool) (out Bool))
    :args (t1 t2 out)
    :requires (((appendLeft or t1 t2) out))
    :conclusion true
)
(step al1 :rule check_appendLeft :args (c1 c2                 (or c1 c2)))
(step al2 :rule check_appendLeft :args (c3 (or c1 c2)         (or (or c3 c1) c2)))
(step al3 :rule check_appendLeft :args (c3 (or (or c1 c1) c2) (or (or (or c3 c1) c1) c2)))
(step al4 :rule check_appendLeft :args (c3 (or c1 (or c1 c2)) (or (or c3 c1) (or c1 c2))))
(step al5 :rule check_appendLeft :args ((or c1 c2)         c3 (or (or c1 c2) c3)))
(step al6 :rule check_appendLeft :args ((or (or c1 c1) c2) c3 (or (or (or c1 c1) c2) c3)))
(step al7 :rule check_appendLeft :args ((or c1 (or c1 c2)) c3 (or (or c1 (or c1 c2)) c3)))

