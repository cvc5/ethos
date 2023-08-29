(include "../theories/Core.smt2")

(declare-sort Int 0)
(declare-sort Real 0)

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

(declare-const + (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U (arith_typeunion T U)) :right-assoc-nil)
(declare-const - (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U (arith_typeunion T U)) :right-assoc-nil)
(declare-const * (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U (arith_typeunion T U)) :right-assoc-nil)

(declare-const < (-> (! Type :var T :requires ((is_arith_type T) true))
                     (! Type :var U :requires ((is_arith_type U) true))
                     Bool) :chainable and)
(declare-const <= (-> (! Type :var T :requires ((is_arith_type T) true))
                      (! Type :var U :requires ((is_arith_type U) true))
                      Bool) :chainable and)
(declare-const > (-> (! Type :var T :requires ((is_arith_type T) true))
                     (! Type :var U :requires ((is_arith_type U) true))
                     Bool) :chainable and)
(declare-const >= (-> (! Type :var T :requires ((is_arith_type T) true))
                      (! Type :var U :requires ((is_arith_type U) true))
                      Bool) :chainable and)

(declare-const to_real (-> (! Type :var T :requires ((is_arith_type T) true))
                           Real))
(declare-const to_int (-> (! Type :var T :requires ((is_arith_type T) true))
                          Int))
(declare-const is_int (-> (! Type :var T :requires ((is_arith_type T) true))
                          Bool))
(declare-const abs (-> (! Type :var T :requires ((is_arith_type T) true))
                       T))
