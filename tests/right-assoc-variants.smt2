
(declare-sort Int 0)
(declare-sort Real 0)
(declare-const BitVec (-> Int Type))
(declare-sort String 0)
(declare-type Seq (Type))

(program maybe_nil ((T Type) (t T) (U Type))
    (T U) T
    (
      ((maybe_nil t t)       t)
      ((maybe_nil t alf.nil) t)
    )
)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-const and
(->
    (! Type :var U :implicit)
    Bool
    U
    (maybe_nil Bool U)
) :right-assoc-nil)


;;;;;; (-> Bool (-> U (maybe_nil Bool U)))
;;;;;; (-> Bool (-> U (Requires (alf.ite (alf.is_eq U alf.nil) Bool U) Bool Bool)))
;;;;;; (-> Bool (-> U (alf.ite (alf.is_eq U alf.nil) Bool (Requires U Bool Bool))))


(declare-const and2
(->
    Bool
    Bool
    Bool
) :right-assoc-nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-const bvand
(->
    (! Type :var U :implicit)
    (! Int :var m :implicit)
    (BitVec m)
    U
    (maybe_nil (BitVec m) U)
) :right-assoc-nil)

;;;;;; (-> (BitVec m) (-> U (maybe_nil (BitVec m) U)))
;;;;;; (-> (BitVec m) (-> U (Requires (alf.ite (alf.is_eq U alf.nil) (BitVec m) U) (BitVec m) (BitVec m))))
;;;;;; (-> (BitVec m) (-> U (alf.ite (alf.is_eq U alf.nil) (BitVec m) (Requires U (BitVec m) (BitVec m)))))

(declare-const bvand2
(->
    (! Int :var m :implicit)
    (BitVec m)
    (BitVec m)
    (BitVec m)
) :right-assoc-nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program arith_typeunion_nary ()
    (Type Type) Type
    (
      ((arith_typeunion_nary Int Real) Real)
      ((arith_typeunion_nary Int Int) Int)
      ((arith_typeunion_nary Int alf.nil) Int)
      ((arith_typeunion_nary Real Real) Real)
      ((arith_typeunion_nary Real Int) Real)
      ((arith_typeunion_nary Real alf.nil) Real)
    )
)

(declare-const +
(->
    (! Type :var T :implicit)
    (! Type :var U :implicit)
    T
    U
    (arith_typeunion_nary T U)
) :right-assoc-nil)

;;;;;; (-> T (-> U (arith_typeunion_nary T U)))
;;;;;; (-> T (-> U (alf.ite (alf.is_eq U alf.nil) (arith_typeunion_nary T U) (Requires U U (arith_typeunion_nary T U)))))
;;;;;; which simplifies to (-> T (-> U (arith_typeunion_nary T U)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program is_string_type ((U Type))
    (Type) Bool
    (
      ((is_string_type String) true)
      ((is_string_type (Seq U)) true)
      ((is_string_type U) false)
    )
)

(declare-const str.++
(->
    (! Type :var T :implicit)
    (! Type :var U :implicit)
    T
    U
    (! T :requires ((is_string_type T) true) :requires ((maybe_nil T U) T))
) :right-assoc-nil)

;;;;;; (-> T (-> U (Requires (is_string_type T) true (Requires (maybe_nil T U) T T))))
;;;;;; (-> T (Requires (is_string_type T) true (-> U (alf.ite (alf.is_eq U alf.nil) T T))))


(declare-const str.++2
(->
    (! Type :var T :implicit)
    (! T :requires ((is_string_type T) true))
    T
    T
) :right-assoc-nil)


; (-> t1 (-> t2 t3)) :right-assoc-nil
;   is
; (-> t1 (-> U (alf.ite (alf.is_eq U alf.nil) t3 (Requires U t2 t3))))

; (-> t1 (-> t2 t3)) :left-assoc-nil
;   is
; (-> U (alf.ite (alf.is_eq U alf.nil) (-> t2 t3) (Requires U t1 (-> t2 t3))))
; ????


;(declare-const = (-> (! Type :var A :implicit) A A Bool) :chainable and)
;(declare-rule refl ((T Type) (x T))
;    :args (x)
;    :conclusion (= x x))
;(step @p0 (= t t) :rule refl :args (t))
