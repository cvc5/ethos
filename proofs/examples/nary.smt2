(include "../theories/Core.smt2")
(include "../programs/Nary.smt2")

(declare-const c1 Bool)
(declare-const c2 Bool)
(declare-const c3 Bool)

; Test append with or
(declare-rule check_append((t1 Bool) (t2 Bool) (out Bool))
    :args (t1 t2 out)
    :requires (((appendOr t1 t2) out))
    :conclusion true
)

(step ap1 :rule check_append :args ((or c1 c2) (or c1 c3) (or c1 c2 c1 c3)))
