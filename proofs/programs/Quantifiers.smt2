(include "../theories/Builtin.smt2")

(program substitute
  ((T Type) (U Type) (S Type) (V Type) (x S) (y S) (f (-> T U)) (a T) (z U) (w V))
  (S S U) U
  (
  ((substitute x y x)             y)
  ((substitute x y (skolem U w))  (skolem U w))   ; do not traverse
  ((substitute x y (f a))         (_ (substitute x y f) (substitute x y a)))
  ((substitute x y z)             z)
  )
)

(program mk_instantiate ((T Type) (x T) (F Bool) (t T) (ts SExpr :list))
  (Bool SExpr) Bool
  (
    ((mk_instantiate (forall x F) (sexpr t ts)) (mk_instantiate (substitute x t F) ts))
    ((mk_instantiate F alf.nil)                 F)
  )
)


(program mk_skolemize ((T Type) (x T) (F Bool) (t T) (ts SExpr :list))
  (Bool) Bool
  (
    ((mk_skolemize F)                 F)
  )
)
