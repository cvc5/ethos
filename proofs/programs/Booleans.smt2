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

; inList cons c l
; Retuns `true` if l inList c.
(program inList
    ((E Type) (L Type) (cons (-> E L L)) (c E) (x E) (xs L :list))
    ((-> E L L) E L) Bool
    (
        ((inList cons c (! E :nil))  false)
        ((inList cons c (cons c xs)) true)
        ((inList cons c (cons x xs)) (inList cons c xs))
    )
)

; ====================================================================
;  Specializations the programs to work with n-ary operators for `or`
; ====================================================================

(program inListOr
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((inListOr c l) (inList or c l)))
)
(program appendOr
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((appendOr c l) (append or c l)))
)
(program concatOr
    ((l1 Bool) (l2 Bool))
    (Bool Bool) Bool
    (((concatOr l1 l2) (concat or l1 l2)))
)
(program removeOr
    ((c Bool) (l Bool))
    (Bool Bool) Bool
    (((removeOr c l) (remove or c l)))
)
(program reverseOr
    ((xs Bool :list))
    (Bool) Bool
    (
        ((reverseOr xs) (reverse or (! Bool :nil) xs))
    )
)
(program naryElimOr
    ((t Bool))
    (Bool) Bool
    (((naryElimOr t) (naryElim or (! Bool :nil) t)))
)
(program naryIntroOr
    ((t Bool))
    (Bool) Bool
    (((naryIntroOr t) (naryIntro or (! Bool :nil) t)))
)

; ==================================================================
;  Specializations the programs to work with n-ary operators for `or`
; ==================================================================

(program inListAnd
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((inListAnd c l) (inList and c l)))
)
(program appendAnd
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((appendAnd c l) (append and c l)))
)
(program concatAnd
    ((l1 Bool) (l2 Bool))
    (Bool Bool) Bool
    (((concatAnd l1 l2) (concat and l1 l2)))
)
(program removeAnd
    ((c Bool) (l Bool))
    (Bool Bool) Bool
    (((removeAnd c l) (remove and c l)))
)
(program reverseAnd
    ((xs Bool :list))
    (Bool) Bool
    (
        ((reverseAnd xs) (reverse and (! Bool :nil) xs))
    )
)
(program naryElimAnd
    ((t Bool))
    (Bool) Bool
    (((naryElimAnd t) (naryElim and (! Bool :nil) t)))
)
(program naryIntroAnd
    ((t Bool))
    (Bool) Bool
    (((naryIntroAnd t) (naryIntro and (! Bool :nil) t)))
)
