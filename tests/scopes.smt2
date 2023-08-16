

(declare-rule contra ((A Bool))
  :premises (false)
  :args (A)
  :conclusion A)


(declare-const B Bool)

(push)
(assume a1 false)
(step a2 B :rule contra :premises (a1) :args (B))
; a3 : (-> (Proof false) (Proof B))
(pop a3 B a2)

(assume a0 false)
(proof B (a3 a0))

(exit)




(push a0 true)
(push a1 false)
(step a2 B :rule contra :premises (a1) :args (B))
; a3 : (-> (Proof false) (Proof B))
(pop a3 B a2)
; a4 : (Proof (=> false B))
(step a4 (=> false B)
  :rule scope
  :assume ((p false))   ; p : (Proof false)
  :premises ((a3 p))
  :args ())
; a5 : (-> (Proof false) (Proof (=> false B)))
(pop a5 (=> false B) a4)
; a6 : (Proof (=> true (=> false B)))
(step a6 (=> true (=> false B))
  :rule scope
  :assume ((p true))   ; p : (Proof true)
  :premises ((a5 p))
  :args ())


(declare-rule scope
  ((F Bool) (G Bool))
  :assume (F)
  :premises (G)
  :args ()
  :conclusion (=> F G)
)

; scope : (-> (Quote F) (Proof G) (Proof (=> F G)))
; (scope false (a3 p))

(declare-rule scope-false
  ((F Bool))
  :assume (F)
  :premises (false)
  :args ()
  :conclusion (not F)
)

; (-> (Proof F) (Proof G))
; (-> (Proof F) (-> (Proof G1) (Proof G2)))

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
