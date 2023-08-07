; ifEqThenElse x y t1 t2
; Returns `t1` if `x` and `y` are the same term.  Otherwise, returns `t2`.
(program ifEqThenElse
    ((U Type) (S Type) (x U) (cmp U) (t1 S) (t2 S))
    (U U S S) S
    (
        ((ifEqThenElse x   x t1 t2) t1)
        ((ifEqThenElse x cmp t1 t2) t2)
    )
)
