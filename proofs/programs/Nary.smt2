; Programs to work with n-ary operators

; ====================================
;  Right-associative null-terminated
; ====================================

; The following functions work with right-associative symbols with a defined
; null terminator.  Those behave somewhat simmilar to functional programming
; lists.  Therefore, the symbol will always be called `cons` in the following
; and the terminator will be `nil`.
; One derivation from lists is that the syntactic suggar cannot be used to
; write unit lists. For example, consider a right-associative `or` with
; `false` as the terminator, then `(or a b c)` correpsonds to
; `(or a (or b (or c false)))`, but `(or a)` is illegal.

; What I need here (generic)
;   - remove
;   - append
;   - intoList
;   - fromList

; append c to the head of l
(program append
    ((U Type) (S Type) (cons (-> U U U)) (c S) (l U :list))
    ((-> U U U) U U) U
    (
        ((append cons c l) (cons c l))
    )
)

; concatinates two lists l1, l2
(program concat
    ((U Type) (S Type) (cons (-> U U U)) (nil U) (l1 U) (l1s U :list) (l2 U))
    ((->  U U U) U U U) U
    (
        ((concat cons nil nil l2) l2)
        ((concat cons nil (cons l1 l1s) l2) (append cons l1 (concat cons nil l1s l2)))
    )
)

; Old stuff

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

