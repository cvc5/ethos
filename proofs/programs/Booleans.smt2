(include "../theories/Core.smt2")

; ifThenElse b t1 t2
; Returns `t1` if `b` is `true`. If it is `false` it returns `t2`.
(program ifThenElse
    ((S Type) (b Bool) (t1 S) (t2 S))
    (Bool S S) S
    (
        ((ifThenElse true  t1 t2) t1)
        ((ifThenElse false t1 t2) t2)
    )
)

; inList cons nil c l
; Retuns `true` if l inList c.
(program inList
    ((U Type) (S Type) (cons (-> S U U)) (nil S) (c S) (x S) (xs U :list))
    ((-> S U U) S U S) Bool
    (
        ((inList cons nil c nil)         false)
        ((inList cons nil c (cons c xs)) true)
        ((inList cons nil c (cons x xs)) (inList cons nil c xs))
    )
)

; ====================================================================
;  Specializations the programs to work with n-ary operators for `or`
; ====================================================================

(program inListOr
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((inListOr c l) (inList or false c l)))
)
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
(program reverseOr
    ((xs Bool :list))
    (Bool) Bool
    (
        ((reverseOr xs) (reverse or false xs))
    )
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
;  Specializations the programs to work with n-ary operators for `or`
; ==================================================================

(program inListAnd
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((inListAnd c l) (inList and true c l)))
)
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
(program reverseAnd
    ((xs Bool :list))
    (Bool) Bool
    (
        ((reverseAnd xs) (reverse and true xs))
    )
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
