(include "../theories/Builtin.smt2")

(declare-sort Int 0)
(declare-sort Real 0)

(declare-consts <numeral> Int)
(declare-consts <decimal> Real)

; used for right-assoc-nil operators, must consider the nil terminator
(program arith_typeunion_nary ()
    (Type Type) Type
    (
      ((arith_typeunion_nary Int Real) Real)
      ((arith_typeunion_nary Int Int) Int)
      ((arith_typeunion_nary Real Real) Real)
      ((arith_typeunion_nary Real Int) Real)
    )
)
(program arith_typeunion ((x Type) (y Type))
    (Type Type) Type
    (
      ((arith_typeunion Int Int) Int)
      ((arith_typeunion Real Real) Real)
      ((arith_typeunion Real Int) Real)
      ((arith_typeunion Int Real) Real)
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
                     T U (arith_typeunion_nary T U)) :right-assoc-nil 0)
(declare-const - (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U (arith_typeunion T U)) :left-assoc)
(declare-const * (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U (arith_typeunion_nary T U)) :right-assoc-nil 1)

(declare-const < (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     (! T :requires ((is_arith_type T) true))
                     (! U :requires ((is_arith_type U) true))
                     Bool)
                     :chainable and)
(declare-const <= (-> (! Type :var T :implicit)
                      (! Type :var U :implicit)
                      (! T :requires ((is_arith_type T) true))
                      (! U :requires ((is_arith_type U) true))
                      Bool)
                      :chainable and)
(declare-const > (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     (! T :requires ((is_arith_type T) true))
                     (! U :requires ((is_arith_type U) true))
                     Bool)
                     :chainable and)
(declare-const >= (-> (! Type :var T :implicit)
                      (! Type :var U :implicit)
                      (! T :requires ((is_arith_type T) true))
                      (! U :requires ((is_arith_type U) true))
                      Bool)
                      :chainable and)

(declare-const to_real (-> (! Type :var T :implicit)
                           (! T :requires ((is_arith_type T) true))
                           Real))
(declare-const to_int (-> (! Type :var T :implicit)
                          (! T :requires ((is_arith_type T) true))
                          Int))
(declare-const is_int (-> (! Type :var T :implicit)
                          (! T :requires ((is_arith_type T) true))
                          Bool))
(declare-const abs (-> (! Type :var T :implicit)
                       (! T :requires ((is_arith_type T) true))
                       T))

; power
(declare-const ^ (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U (arith_typeunion T U)))

; currently unary negation cannot use overload
(declare-const u- (-> (! Type :var T :implicit)
                      (! T :requires ((is_arith_type T) true))
                      T))
