(include "../programs/Quantifiers.smt2")
(include "../theories/Quantifiers.smt2")


(declare-rule instantiate ((F Bool) (xs @List) (ts @List))
  :premises ((forall xs F))
  :args (ts)
  :conclusion (substitute_list xs ts F))

; returns the list of skolems for F
(program mk_skolems ((x @List) (xs @List :list) (F Bool))
  (@List Bool) @List
  (
  ((mk_skolems (@list x xs) F) (@list (skolem (@k.QUANTIFIERS_SKOLEMIZE F x)) (mk_skolems xs F)))
  ((mk_skolems alf.nil F)      alf.nil)
  )
)

(declare-rule skolemize ((F Bool))
  :premises (F)
  :conclusion
    (alf.match ((T Type) (x @List) (G Bool))
        F
        ((exists x G)       (substitute_list x (mk_skolems x F) G))
        ((not (forall x G)) (substitute_list x (mk_skolems x (exists x (not G))) (not G)))))
