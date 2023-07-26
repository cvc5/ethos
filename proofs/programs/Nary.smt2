; Programs to work with n-ary operators

; What I need here (generic)
;   - remove
;   - append
;   - intoList
;   - fromList


; append t1 to t2 if t1 and t2 are null-terminated lists
(program append
    ((U Type) (f (-> U U U)) (t1 U) (t2 U :list))
    ((-> U U U) U U) U
    (
        ((append f t1 t2) (f t1 t2))
    )
)

(program appendLeft
    ((U Type) (f (-> U U U)) (t1 U :list) (t2 U))
    ((-> U U U) U U) U
    (
        ((appendLeft f t1 t2) (f t1 t2))
    )
)

(program appendOr
    ((t1 Bool) (t2 Bool :list))
    (Bool Bool) Bool
    (
        ((appendOr t1 t2) (or t1 t2))
    )
)

; removeRight t u
; Remove the first occurence of t from a term u = (f c1 (f c2 ..))
(program removeRight ((T Type) (f (-> T T T)) (t T) (u T) (c T))
    (T T) T
    (
        ((removeRight t (f u t)) u)
        ((removeRight t (f t u)) u)
        ((removeRight t (f c u)) (f c (removeRight t u)))
        ((removeRight t c) c)
    )
)

; appendRight f t1 t2
; Appends a term t2 to a term t1 = (f c1 (f c2 ..)) where f is a
; right-assocative function symbol.
(program appendRight ((T Type) (f (-> T T T)) (t1 T) (ts1 T) (t2 T) (ts2 T))
    ((-> T T T) T T) T
    (
        ((appendRight f (f t1 ts1) ts2) (f t1 (appendRight f ts1 ts2)))
        ((appendRight f        t1  ts2) (f t1                    ts2 ))
    )
)

; removeLeft t u
; Remove the first occurence of t from a term u = f (f (f ... c1) c2 .. )
(program removeLeft ((T Type) (f (-> T T T)) (t T) (u T) (c T))
    (T T) T
    (
        ((removeLeft t (f t u)) u)
        ((removeLeft t (f u t)) u)
        ((removeLeft t (f u c)) (f (removeLeft t u) c))
        ((removeLeft t c) c)
    )
)

; appendLeft t1 t2
; Appends a term t2 = (f (f .. c1) c2 ..) to a term t1 where f is a
; left-assocative function symbol.
; (program appendLeft ((T Type) (f (-> T T T)) (t1 T) (ts1 T) (t2 T) (ts2 T))
;     ((-> T T T) T T) T
;     (
;         ((appendLeft f t1 (f ts2 t2)) (f (appendLeft f t1 ts2) t2))
;         ((appendLeft f t1        ts2) (f t1                   ts2))
;     )
; )

