(include "../theories/Builtin.smt2")
(include "../theories/Arith.smt2")

(declare-sort String 0)
(declare-sort RegLan 0)
(declare-type Seq (Type))

(declare-consts <string> String)

(program is_string_type ((U Type))
    (Type) Bool
    (
      ((is_string_type String) true)
      ((is_string_type (Seq U)) true)
      ((is_string_type U) false)
    )
)

; core
(declare-const str.len (-> (! Type :var T :implicit)
                           T
                           (! Int :requires ((is_string_type T) true))))
(declare-const str.++ (-> (! Type :var T :implicit) (! Type :var U :implicit)
                          T U
                          (! T :requires ((is_string_type T) true) 
                               :requires ((maybe_nil T U) T))) :right-assoc-nil)

; extended functions
(declare-const str.substr (-> (! Type :var T :implicit)
                              T Int Int
                              (! T :requires ((is_string_type T) true))))
(declare-const str.contains (-> (! Type :var T :implicit)
                                T T
                                (! Bool :requires ((is_string_type T) true))))
(declare-const str.replace (-> (! Type :var T :implicit)
                               T T T
                               (! T :requires ((is_string_type T) true))))
(declare-const str.indexof (-> (! Type :var T :implicit)
                               T T Int
                               (! Int :requires ((is_string_type T) true))))
(declare-const str.at (-> String Int String))
(declare-const str.prefixof (-> String String Bool))
(declare-const str.suffixof (-> String String Bool))
(declare-const str.rev (-> String String))
(declare-const str.unit (-> Int String))
(declare-const str.update (-> String String String String))
(declare-const str.to_lower (-> String String))
(declare-const str.to_upper (-> String String))
(declare-const str.to_code (-> String Int))
(declare-const str.from_code (-> Int String))
(declare-const str.is_digit (-> String Bool))
(declare-const str.to_int (-> String Int))
(declare-const str.from_int (-> Int String))
(declare-const str.< (-> String String Bool))
(declare-const str.<= (-> String String Bool))
(declare-const str.replace_all (-> String String String String))
(declare-const str.replace_re (-> String RegLan String String))
(declare-const str.replace_re_all (-> String RegLan String String))

; regular expressions
(declare-const re.allchar RegLan)
(declare-const re.none RegLan)
(declare-const re.all RegLan)
(declare-const re.empty RegLan)
(declare-const str.to_re (-> String RegLan))
(declare-const re.* (-> RegLan RegLan))
(declare-const re.+ (-> RegLan RegLan))
(declare-const re.opt (-> RegLan RegLan))
(declare-const re.comp (-> RegLan RegLan))
(declare-const re.range (-> String String RegLan))
(declare-const re.++ (-> (! Type :var U :implicit) RegLan U (! RegLan :requires ((maybe_nil RegLan U) RegLan))) :right-assoc-nil)
(declare-const re.inter (-> (! Type :var U :implicit) RegLan U (! RegLan :requires ((maybe_nil RegLan U) RegLan))) :right-assoc-nil)
(declare-const re.union (-> (! Type :var U :implicit) RegLan U (! RegLan :requires ((maybe_nil RegLan U) RegLan))) :right-assoc-nil)
(declare-const re.diff (-> (! Type :var U :implicit) RegLan U (! RegLan :requires ((maybe_nil RegLan U) RegLan))) :right-assoc-nil)
(declare-const re.loop (-> Int Int RegLan RegLan))
(declare-const str.in_re (-> String RegLan Bool))


; Sequences
(declare-const seq.empty (-> (! Type :var T) T))
(declare-const seq.unit (-> (! Type :var T :implicit) T (Seq T)))
(declare-const seq.nth (-> (! Type :var T :implicit) (Seq T) T))
(declare-const seq.len (-> (! Type :var T :implicit) (Seq T) Int))

;(declare f_seq.++ term)
;(define seq.++ (# x term (# y term (apply (apply f_seq.++ x) y))))
;(declare f_seq.extract term)
;(define seq.extract (# x term (# y term (# z term (apply (apply (apply f_seq.extract x) y) z)))))
;(declare f_seq.contains term)
;(define seq.contains (# x term (# y term (apply (apply f_seq.contains x) y))))
;(declare f_seq.replace term)
;(define seq.replace (# x term (# y term (# z term (apply (apply (apply f_seq.replace x) y) z)))))
;(declare f_seq.indexof term)
;(define seq.indexof (# x term (# y term (# z term (apply (apply (apply f_seq.indexof x) y) z)))))
;(declare f_seq.prefixof term)
;(define seq.prefixof (# x term (# y term (apply (apply f_seq.prefixof x) y))))
;(declare f_seq.suffixof term)
;(define seq.suffixof (# x term (# y term (apply (apply f_seq.suffixof x) y))))
;(declare f_seq.rev term)
;(define seq.rev (# x term (apply f_seq.rev x)))
;(declare f_seq.update term)
;(define seq.update (# x term (# y term (# z term (apply (apply (apply f_seq.update x) y) z)))))



; skolems
(declare-const @k.RE_UNFOLD_POS_COMPONENT (-> String RegLan Int String))
