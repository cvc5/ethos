

(declare-rule contra ((A Bool))
  :premises (false)
  :args (A)
  :conclusion A)


(declare-const B Bool)

(assume a0 false)

(push)
(assume a1 false)
(step a2 B :rule contra :premises (a1) :args (B))
; a3 : (-> (Proof false) (Proof B))
(pop a3 B a2)

(proof B (a3 a0))

(exit)

; maybe this?
(declare-const scope
  (-> (! Bool :var F)
      (! Bool :var G)
      (-> (Proof F) (Proof G))
      (Proof (=> F G))))
(declare-const scope-false
  (-> (! Bool :var F)
      (-> (Proof F) (Proof false))
      (Proof (not F))))

(define-proof a4 () (=> F G) (scope a3))
