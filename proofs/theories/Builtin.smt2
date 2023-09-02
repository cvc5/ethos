; cvc5-specific

(declare-const skolem (-> (! Type :var A :implicit) A A))

; We construct all skolems by wrapping them in an application of `skolem`.
; The argument is either
; (1) an application of an internal function symbol @k.ID where ID is the
; skolem function id, 
; (2) a term t, in the case of purify skolems, where t is the term.

; For example, the array diff skolem for arrays A and B is:
;   (skolem (@k.ARRAY_DIFF A B))
; where we have:
;   (declare-const @k.ARRAY_DIFF 
;      (-> (! Type :var T :implicit) (! Type :var U :implicit) (Array T U) (Array T U) T))



; generic variables
; NOTE: does not check that U is a numeral
(declare-const const (-> (! Type :var U :implicit) U (! Type :var T) T))
(declare-const var (-> (! Type :var U :implicit) U (! Type :var T) T))
