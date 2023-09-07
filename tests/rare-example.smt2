(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(declare-const and (-> Bool Bool Bool) :left-assoc-nil true)

(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)

(declare-axiom bool-or-true ((xs Bool :list) (ys Bool :list))
  (= (or xs true ys) true)
)

(declare-axiom bool-or-false ((xs Bool :list) (ys Bool :list))
  (= (or xs false ys) (alf.from_list or (or xs ys)))
)

(step @p0 (= (or a b true c) true) :rule bool-or-true :args ((or a b) (alf.cons or c false)))
(step @p1 (= (or a true) true) :rule bool-or-true :args ((alf.cons or a false) false))
(step @p2 (= (or (or a b) true) true) :rule bool-or-true :args ((alf.cons or (or a b) false) false))

(step @p3 (= (or a b false c) (or a b c)) :rule bool-or-false :args ((or a b) (alf.cons or c false)))
(step @p4 (= (or a false) a) :rule bool-or-false :args ((alf.cons or a false) false))
(step @p5 (= (or (or a b) false) (or a b)) :rule bool-or-false :args ((alf.cons or (or a b) false) false))

(declare-axiom bool-and-true ((xs Bool :list) (ys Bool :list))
  (= (and xs true ys) (alf.from_list and (and xs ys)))
)

(declare-axiom bool-and-false ((xs Bool :list) (ys Bool :list))
  (= (and xs false ys) false)
)

(step @p6 (= (and a b false c) false) :rule bool-and-false :args ((and a b) (alf.cons and true c)))
(step @p7 (= (and a false) false) :rule bool-and-false :args ((alf.cons and true a) true))
(step @p8 (= (and (and a b) false) false) :rule bool-and-false :args ((alf.cons and true (and a b)) true))

(step @p9 (= (and a b true c) (and a b c)) :rule bool-and-true :args ((and a b) (alf.cons and true c)))
(step @p10 (= (and a true) a) :rule bool-and-true :args ((alf.cons and true a) true))
(step @p11 (= (and (and a b) true) (and a b)) :rule bool-and-true :args ((alf.cons and true (and a b)) true))

