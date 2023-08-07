(declare-const true Bool)
(declare-const false Bool)

(declare-rule contra ((A Bool))
  :premises (false)
  :args (A)
  :conclusion A)


(declare-const B Bool)

(assume a0 false)

(push)
(assume a1 false)
(step a2 B :rule contra :premises (a1) :args (B))
(pop a3 B a2)


(proof B (a3 a0))
