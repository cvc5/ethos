(include "../theories/Core.smt2")

(declare-sort Int 0)
(declare-sort Real 0)

(declare-consts <numeral> Int)
(declare-consts <decimal> Real)

(program arith_typeunion ()
    (Type Type) Type
    (
      ((arith_typeunion Int Int) Int)
      ((arith_typeunion Int Real) Real)
      ((arith_typeunion Real Int) Real)
      ((arith_typeunion Real Real) Real)
    )
)

(program is_arith_type ((x Type))
    (Type) Bool
    (
      ((is_arith_type Int) true)
      ((is_arith_type Real) true)
    )
)

; Must use integer nil terminators to avoid confusion with subtyping
(declare-const + (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U (arith_typeunion T U)) :right-assoc 0)
(declare-const - (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U (arith_typeunion T U)) :right-assoc 0)
(declare-const * (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U (arith_typeunion T U)) :right-assoc 1)

(declare-const < (-> (! Type :var T :implicit :requires ((is_arith_type T) true))
                     (! Type :var U :implicit :requires ((is_arith_type U) true))
                     T U Bool) :chainable and)
(declare-const <= (-> (! Type :var T :implicit :requires ((is_arith_type T) true))
                      (! Type :var U :implicit :requires ((is_arith_type U) true))
                      T U Bool) :chainable and)
(declare-const > (-> (! Type :var T :implicit :requires ((is_arith_type T) true))
                     (! Type :var U :implicit :requires ((is_arith_type U) true))
                     T U Bool) :chainable and)
(declare-const >= (-> (! Type :var T :implicit :requires ((is_arith_type T) true))
                      (! Type :var U :implicit :requires ((is_arith_type U) true))
                      T U Bool) :chainable and)

(declare-const to_real (-> (! Type :var T :implicit :requires ((is_arith_type T) true))
                           T Real))
(declare-const to_int (-> (! Type :var T :implicit :requires ((is_arith_type T) true))
                          T Int))
(declare-const is_int (-> (! Type :var T :implicit :requires ((is_arith_type T) true))
                          T Bool))
(declare-const abs (-> (! Type :var T :implicit :requires ((is_arith_type T) true))
                       T T))

; currently unary negation cannot use overload
(declare-const u- (-> (! Type :var T :implicit :requires ((is_arith_type T) true))
                       T T))
