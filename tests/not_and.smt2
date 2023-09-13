(include "Builtin-theory.smt2")
(include "Nary.smt2")

; NOT_AND
(program lowerNot ((l Bool) (ls Bool :list))
    (Bool) Bool
    (
        ((lowerNot true)           false)
        ((lowerNot (and l ls))     (alf.cons or (not l) (lowerNot ls)))
    )
)

(declare-rule not_and ((F Bool))
    :premises ((not F))
    :conclusion (lowerNot F)
)

; not_and
(declare-const c1 Bool)
(declare-const c2 Bool)
(assume notanda1 (not (and c1 c2 (not c2))))
(step   notandt1 (or (not c1) (not c2) (not (not c2))) :rule not_and :premises (notanda1))
