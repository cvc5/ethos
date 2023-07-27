; Programs to work with n-ary operators

(include "../theories/Core.smt2")

; ====================================
;  Right-associative null-terminated
; ====================================

; The following functions work with right-associative symbols with a defined
; null terminator.  Those behave somewhat similar to functional programming
; lists.  Therefore, the symbol will always be called `cons` in the following
; and the terminator will be `nil`.
; One derivation from lists is that the syntactic sugar cannot be used to
; write unit lists. For example, consider a right-associative `or` with
; `false` as the terminator, then `(or a b c)` corresponds to
; `(or a (or b (or c false)))`, but `(or a)` is illegal.

; append c to the head of l
(program append
    ((U Type) (S Type) (cons (-> S U U)) (c S) (l U :list))
    ((-> S U U) S U) U
    (
        ((append cons c l) (cons c l))
    )
)

; concatenate two lists l1, l2
(program concat
    ((U Type) (S Type) (cons (-> S U U)) (nil S) (l1 U) (l1s U :list) (l2 U))
    ((-> S U U) S U U) U
    (
        ((concat cons nil nil l2) l2)
        ((concat cons nil (cons l1 l1s) l2) (append cons l1 (concat cons nil l1s l2)))
    )
)

; remove the first occurence of c from l
(program remove
    ((U Type) (S Type) (cons (-> S U U)) (nil S) (c S) (cp S) (l U :list))
    ((-> S U U) S S U) U
    (
        ((remove cons nil c nil) nil)
        ((remove cons nil c (cons c l)) l)
        ((remove cons nil c (cons cp l)) (append cons cp (remove cons nil c l)))
    )
)

; TODO: move to other header with general helpers
(program ifEqThenElse
    ((U Type) (S Type) (x U) (cmp U) (t1 S) (t2 S))
    (U U S S) S
    (
        ((ifEqThenElse x   x t1 t2) t1)
        ((ifEqThenElse x cmp t1 t2) t2)
    )
)

; returns the sole elment if l is singleton list
(program naryElim
    ((U Type) (S Type) (cons (-> U U U)) (nil U) (l U) (ls U :list))
    ((-> U U U) U U) U
    (
        ((naryElim cons nil (cons l ls)) (ifEqThenElse ls nil l (cons l ls)))
        ((naryElim cons nil l) l)
    )
)

; returns a singleton list if the argument is not
(program naryIntro
    ((U Type) (S Type) (cons (-> U U U)) (nil U) (c U) (l U :list))
    ((-> U U U) U U) U
    (
        ((naryIntro cons nil (cons c l)) (cons c l))
        ((naryIntro cons nil c) (@ (cons c) nil))
    )
)

; ==================================================================
;        Specializations of the functions above for `or`
; ==================================================================

(program appendOr
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((appendOr c l) (append or c l)))
)
(program concatOr
    ((l1 Bool) (l2 Bool))
    (Bool Bool) Bool
    (((concatOr l1 l2) (concat or false l1 l2)))
)
(program removeOr
    ((c Bool) (l Bool))
    (Bool Bool) Bool
    (((removeOr c l) (remove or false c l)))
)
(program naryElimOr
    ((t Bool))
    (Bool) Bool
    (((naryElimOr t) (naryElim or false t)))
)
(program naryIntroOr
    ((t Bool))
    (Bool) Bool
    (((naryIntroOr t) (naryIntro or false t)))
)

; ==================================================================
;        Specializations of the functions above for `and`
; ==================================================================

(program appendAnd
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((appendAnd c l) (append and c l)))
)
(program concatAnd
    ((l1 Bool) (l2 Bool))
    (Bool Bool) Bool
    (((concatAnd l1 l2) (concat and true l1 l2)))
)
(program removeAnd
    ((c Bool) (l Bool))
    (Bool Bool) Bool
    (((removeAnd c l) (remove and true c l)))
)
(program naryElimAnd
    ((t Bool))
    (Bool) Bool
    (((naryElimAnd t) (naryElim and true t)))
)
(program naryIntroAnd
    ((t Bool))
    (Bool) Bool
    (((naryIntroAnd t) (naryIntro and true t)))
)
