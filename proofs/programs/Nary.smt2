; Programs to work with n-ary operators

(include "../programs/Utils.smt2")

; =============================================
;  Right-associative null-terminated operators
; =============================================
; The following functions work with right-associative symbols with a defined
; null terminator.  Those behave somewhat similar to functional programming
; lists.  Therefore, the symbol will always be called `cons` in the following
; and the terminator will be `nil`.
;
; The AletheLF syntactic sugar for n-ary operators introduces some behavior
; that can be counter intuitive:
; 1) Consider a pattern `(cons x xs)` where `xs` is annotated with `:list`.
;    In this case building the term `(cons x xs)` will not result in the
;    term that matched the pattern.  This is because `(cons x xs)` is
;    syntactic sugar for `(cons x (cons xs nil))`.  Note that, xs here
;    is not the tail of the list.  It is just an element.
; 2) It is not possible to directly build unit lists, since `(cons x)` is
;    not valid.
;
; Both cases can be addressed by using the `append` function defined below.
; A call `(append x xs)` will create the list from point 1 and `(append x nil)`
; will create a unit list.

; append cons nil c l
; Appends c to the head of l.
(program append
    ((U Type) (S Type) (cons (-> S U U)) (c S) (l U :list))
    ((-> S U U) S U) U
    (
        ((append cons c l) (cons c l))
    )
)

; concat cons nil l1 l2
; Concatenates two lists l1 and l2.
(program concat
    ((U Type) (S Type) (cons (-> S U U)) (nil S) (l1 U) (l1s U :list) (l2 U))
    ((-> S U U) S U U) U
    (
        ((concat cons nil nil l2) l2)
        ((concat cons nil (cons l1 l1s) l2) (append cons l1 (concat cons nil l1s l2)))
    )
)

; remove cons nil c l
; Removes the first occurrence of c from l.
(program remove
    ((U Type) (S Type) (cons (-> S U U)) (nil S) (c S) (cp S) (l U :list))
    ((-> S U U) S S U) U
    (
        ((remove cons nil c nil) nil)
        ((remove cons nil c (cons c l)) l)
        ((remove cons nil c (cons cp l)) (append cons cp (remove cons nil c l)))
    )
)

; naryElim cons nil l
; Returns the sole element if l is a singleton list.
(program naryElim
    ((U Type) (S Type) (cons (-> U U U)) (nil U) (l U) (ls U :list))
    ((-> U U U) U U) U
    (
        ((naryElim cons nil (cons l ls)) (ifEqThenElse ls nil l (cons l ls)))
        ((naryElim cons nil l) l)
    )
)

; naryIntro cons nil l
; Returns a singleton list if c is not a list.
(program naryIntro
    ((U Type) (S Type) (cons (-> U U U)) (nil U) (c U) (l U :list))
    ((-> U U U) U U) U
    (
        ((naryIntro cons nil (cons c l)) (cons c l))
        ((naryIntro cons nil c) (append cons c nil))
    )
)
