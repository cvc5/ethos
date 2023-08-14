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

; append cons c xs
; Appends `c` to the head of `xs`.
(program append
    ((L Type) (E Type) (cons (-> E L L)) (c E) (xs L :list))
    ((-> E L L) E L) L
    (
        ((append cons c xs) (cons c xs))
    )
)

; concat cons xs ys
; Concatenates two lists `xs` and `ys`.
(program concat
    ((L Type) (E Type) (cons (-> E L L)) (x L) (xs L :list) (ys L))
    ((-> E L L) L L) L
    (
        ((concat cons (! E :nil) ys) ys)
        ((concat cons (cons x xs) ys) (append cons x (concat cons xs ys)))
    )
)

; remove cons c xs
; Removes the first occurrence of `c` from `xs`.
(program remove
    ((L Type) (E Type) (cons (-> E L L)) (c E) (y E) (xs L :list))
    ((-> E L L) E L) L
    (
        ((remove cons c (! E :nil)) (! E :nil))
        ((remove cons c (cons c xs)) xs)
        ((remove cons c (cons y xs)) (append cons y (remove cons c xs)))
    )
)

; Helper for reverse
(program reverseRec
    ((L Type) (E Type) (cons (-> E L L)) (x L) (xs L :list) (l L :list))
    ((-> E L L) L L) L
    (
        ((reverseRec cons (! E :nil)  l)  l)
        ((reverseRec cons (cons x xs) l) (reverseRec cons xs (append cons x l)))
    )
)

; reverse cons nil xs
; Reverses the list `xs`.
(program reverse
    ((L Type) (E Type) (cons (-> E L L)) (nil L) (xs L :list))
    ((-> E L L) L L) L
    (
        ((reverse cons nil xs) (reverseRec cons xs nil))
    )
)

; naryElim cons x
; Returns the sole element if `xs` is a singleton list.
(program naryElim
    ((L Type) (cons (-> L L L)) (nil L) (x L) (xs L :list))
    ((-> L L L) L L) L
    (
        ((naryElim cons nil (cons x nil)) x)
        ((naryElim cons nil (cons x xs)) (append cons x xs))
        ((naryElim cons nil xs) xs)
    )
)

; naryIntro cons x
; Returns a singleton list if `x` is not a list.
(program naryIntro
    ((L Type) (cons (-> L L L)) (nil L) (x L) (xs L :list))
    ((-> L L L) L L) L
    (
        ((naryIntro cons nil (cons x xs)) (append cons x xs))
        ((naryIntro cons nil x)           (append cons x nil))
    )
)
