

(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const or (-> Bool Bool Bool) :right-assoc-nil)
(declare-const and (-> Bool Bool Bool) :left-assoc-nil)

(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)


(declare-rule bool-or-true ((xs Bool :list) (ys Bool :list))
  :args (xs ys)
  :conclusion (= (or xs true ys) true)
)

(declare-rule bool-or-false ((xs Bool :list) (ys Bool :list))
  :args (xs ys)
  :conclusion (= (or xs false ys) (or xs ys))
)

(step @p0 (= (or a b true c) true) :rule bool-or-true :args ((or a b) (or c alf.nil)))
(step @p1 (= (or a true) true) :rule bool-or-true :args ((or a alf.nil) alf.nil))
(step @p2 (= (or (or a b) true) true) :rule bool-or-true :args ((or (or a b) alf.nil) alf.nil))

(step @p3 (= (or a b false c) (or a b c)) :rule bool-or-false :args ((or a b) (or c alf.nil)))
(step @p4 (= (or a false) a) :rule bool-or-false :args ((or a alf.nil) alf.nil))
(step @p5 (= (or (or a b) false) (or a b)) :rule bool-or-false :args ((or (or a b) alf.nil) alf.nil))



(declare-rule bool-and-true ((xs Bool :list) (ys Bool :list))
  :args (xs ys)
  :conclusion (= (and xs true ys) (and xs ys))
)

(declare-rule bool-and-false ((xs Bool :list) (ys Bool :list))
  :args (xs ys)
  :conclusion (= (and xs false ys) false)
)



(step @p6 (= (and a b false c) false) :rule bool-and-false :args ((and a b) (and alf.nil c)))
(step @p7 (= (and a false) false) :rule bool-and-false :args ((and alf.nil a) alf.nil))
(step @p8 (= (and (and a b) false) false) :rule bool-and-false :args ((and alf.nil (and a b)) alf.nil))

(step @p9 (= (and a b true c) (and a b c)) :rule bool-and-true :args ((and a b) (and alf.nil c)))
(step @p10 (= (and a true) a) :rule bool-and-true :args ((and alf.nil a) alf.nil))
(step @p11 (= (and (and a b) true) (and a b)) :rule bool-and-true :args ((and alf.nil (and a b)) alf.nil))

