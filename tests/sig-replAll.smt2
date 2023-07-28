
(declare-const false Bool)
(declare-const = (-> (! Type :var T :implicit) T T Bool))

(declare-const or (-> Bool Bool Bool) :right-assoc)

(program replAll 
  ((x Bool) (y Bool) (z Bool) (tail Bool :list))
  (Bool Bool Bool) Bool
  ; cases
  (
  ((replAll x y (or x tail)) (or y (replAll x y tail)))
  ((replAll x y (or z tail)) (or z (replAll x y tail)))
  ((replAll x y z)           z)
  )
)

(declare-rule or_repl-all 
   ((f Bool) (a Bool) (b Bool))
   :premises (f (= a b))
   :args ()
   :conclusion (replAll a b f)
)


