
(declare-const => (-> Bool Bool Bool))

(declare-rule contra ((A Bool))
  :premises (false)
  :args (A)
  :conclusion A)


(declare-const B Bool)

(declare-rule scope
  ((F Bool) (G Bool))
  :assumption F
  :premises (G)
  :args ()
  :conclusion (=> F G)
)

(push a0 true)
(push a1 false)
(step a2 B :rule contra :premises (a1) :args (B))
; a3 : (-> (Proof false) (Proof B))
(pop a3 (=> false B)
  :rule scope
  :premises (a2)
  :args ())
; a4 : (Proof (=> true (=> false B)))
(pop a4 (=> true (=> false B))
  :rule scope
  :premises (a3)
  :args ())

(exit)

