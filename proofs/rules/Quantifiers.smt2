(include "../programs/Quantifiers.smt2")
(include "../theories/Quantifiers.smt2")

(declare-rule instantiate ((F Bool) (ts SExpr))
  :premises (F)
  :args (ts)
  :conclusion (mk_instantiate F ts))

(declare-rule skolemize ((F Bool) (ts SExpr))
  :premises (F)
  :args (ts)
  :conclusion
    (alf.match ((T Type) (x T) (G Bool))
        F
        ((exists x G)       (mk_skolemize F F ts))
        ((not (forall x G)) (not (mk_skolemize (forall x G) (forall x G) ts)))))
