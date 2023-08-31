
(declare-const = (-> (! Type :var A :implicit) A A Bool))

; note that U is bound before x is parsed
(define-fun eq ((U Type) (x U)) Bool (= x x))

