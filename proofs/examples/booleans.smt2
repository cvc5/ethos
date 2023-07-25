(include "../rules/Booleans.smt2")

(declare-const c1 Bool)
(declare-const c2 Bool)
(declare-const c3 Bool)

; Resolution
(assume a1 (or      c1  c2))
(assume a2 (or (not c2) c3))
(assume a3 (not c2))

(step t1 (or c1 c3) :rule resolution :premises (a1 a2) :args (true c2))
(step t2 (or c3 c1) :rule resolution :premises (a2 a1) :args (false c2))

(step t3 c1 :rule resolution :premises (a1 a3) :args (true c2))

; Factoring
(assume faca1 (or (or (or (or c1 c1) c2) (not c2)) (not c2)))
(step   fact1         (or (or c1     c2)           (not c2))                 :rule factoring :premises (faca1))
(assume faca2 (or (or (or (or (or c1 c1) (or c1 c2)) (not c2)) (not c2)) c1))
(step   fact2         (or (or (or c1     (or c1 c2))           (not c2)) c1) :rule factoring :premises (faca2))

; Reordering
(assume reord1 (and c1 c2))
(step  reordt1 :rule reordering :premises (reord1) :args ((and c1 c2)))

(assume reord2 (or c1 c2))
(step  reordt2 :rule reordering :premises (reord2) :args ((or c2 c1)))

; Reorder c1, c1, (or c1 c2), (not c2), (not c2), c1
;      to (or c1 c2), c1, (not c2), c1, (not c2), c1
(assume reord3 (or (or (or (or (or c1 c1) (or c1 c2)) (not c2)) (not c2)) c1))
(step  reordt3 :rule reordering :premises (reord3) :args ((or (or (or (or (or (or c1 c2) c1) (not c2)) c1) (not c2)) c1)))

