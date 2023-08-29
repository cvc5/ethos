(include "../theories/Core.smt2")


; ====================================================================
;  Specializations the programs to work with n-ary operators for `or`
; ====================================================================

(program inListOr
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((inListOr c l) (nary.ctn or c l)))
)
(program appendOr
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((appendOr c l) (nary.append or c l)))
)
(program concatOr
    ((l1 Bool) (l2 Bool))
    (Bool Bool) Bool
    (((concatOr l1 l2) (nary.concat or l1 l2)))
)
(program removeOr
    ((c Bool) (l Bool))
    (Bool Bool) Bool
    (((removeOr c l) (nary.remove or c l)))
)
(program reverseOr
    ((xs Bool :list))
    (Bool) Bool
    (
        ((reverseOr xs) (nary.reverse or (alf.nil Bool) xs))
    )
)
(program naryElimOr
    ((t Bool))
    (Bool) Bool
    (((naryElimOr t) (nary.elim or (alf.nil Bool) false t)))
)
(program naryIntroOr
    ((t Bool))
    (Bool) Bool
    (((naryIntroOr t) (nary.intro or (alf.nil Bool) t)))
)

; ==================================================================
;  Specializations the programs to work with n-ary operators for `or`
; ==================================================================

(program inListAnd
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((inListAnd c l) (nary.ctn and c l)))
)
(program appendAnd
    ((c Bool) (l Bool :list))
    (Bool Bool) Bool
    (((appendAnd c l) (nary.append and c l)))
)
(program concatAnd
    ((l1 Bool) (l2 Bool))
    (Bool Bool) Bool
    (((concatAnd l1 l2) (nary.concat and l1 l2)))
)
(program removeAnd
    ((c Bool) (l Bool))
    (Bool Bool) Bool
    (((removeAnd c l) (nary.remove and c l)))
)
(program reverseAnd
    ((xs Bool :list))
    (Bool) Bool
    (
        ((reverseAnd xs) (nary.reverse and (alf.nil Bool) xs))
    )
)
(program naryElimAnd
    ((t Bool))
    (Bool) Bool
    (((naryElimAnd t) (nary.elim and (alf.nil Bool) true t)))
)
(program naryIntroAnd
    ((t Bool))
    (Bool) Bool
    (((naryIntroAnd t) (nary.intro and (alf.nil Bool) t)))
)
