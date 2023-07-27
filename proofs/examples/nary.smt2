(include "../programs/Nary.smt2")

(declare-const true Bool)

(declare-type S    ())
(declare-type List ())

(declare-const nil S)
(declare-const cons (-> S S S)
    :right-assoc nil
)

(declare-const c1 S)
(declare-const c2 S)
(declare-const c3 S)


(declare-rule check_append((c S) (l S) (out S))
    :args (c l out)
    :requires (((append cons c l) out))
    :conclusion true
)

(step ap1 :rule check_append :args (c3 (cons c1 c2) (cons c3 c1 c2)))


(declare-rule check_concat((t1 S) (t2 S) (out S))
    :args (t1 t2 out)
    :requires (((concat cons nil t1 t2) out))
    :conclusion true
)

(step co1 :rule check_concat :args (nil (cons c1 c3) (cons c1 c3)))
(step co2 :rule check_concat :args ((cons c1 c2) (cons c1 c3) (cons c1 c2 c1 c3)))


