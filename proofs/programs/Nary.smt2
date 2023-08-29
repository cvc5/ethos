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

; nary.append cons c xs
; Appends `c` to the head of `xs`.
(program nary.append
    ((L Type) (cons (-> L L L)) (c L) (xs L :list))
    ((-> L L L) L L) L
    (
        ((nary.append cons c xs) (cons c xs))
    )
)

; nary.ctn cons c l
; Retuns `true` if l inList c.
(program nary.ctn
    ((L Type) (cons (-> L L L)) (c L) (x L) (xs L :list))
    ((-> L L L) L L) Bool
    (
        ((nary.ctn cons c (alf.nil L)) false)
        ((nary.ctn cons c (cons c xs)) true)
        ((nary.ctn cons c (cons x xs)) (nary.ctn cons c xs))
    )
)

; nary.is_subset cons c l
; Retuns `true` if l nary.ctn c.
(program nary.is_subset
    ((L Type) (cons (-> L L L)) (c L) (t L) (xs L :list))
    ((-> L L L) L L) Bool
    (
        ((nary.is_subset cons (alf.nil L) t) true)
        ((nary.is_subset cons (cons c xs) t) (alf.ite (nary.ctn cons c t) (nary.is_subset cons xs t) false))
    )
)

; concat cons xs ys
; Concatenates two lists `xs` and `ys`.
(program nary.concat
    ((L Type) (cons (-> L L L)) (x L) (xs L :list) (ys L))
    ((-> L L L) L L) L
    (
        ((nary.concat cons (alf.nil L) ys) ys)
        ((nary.concat cons (cons x xs) ys) (nary.append cons x (nary.concat cons xs ys)))
    )
)

; remove cons c xs
; Removes the first occurrence of `c` from `xs`.
(program nary.remove
    ((L Type) (cons (-> L L L)) (c L) (y L) (xs L :list))
    ((-> L L L) L L) L
    (
        ((nary.remove cons c (alf.nil L)) (alf.nil L))
        ((nary.remove cons c (cons c xs)) xs)
        ((nary.remove cons c (cons y xs)) (nary.append cons y (nary.remove cons c xs)))
    )
)

; Helper for reverse
(program nary.reverseRec
    ((L Type) (cons (-> L L L)) (x L) (xs L :list) (l L :list))
    ((-> L L L) L L) L
    (
        ((nary.reverseRec cons (alf.nil L)  l)  l)
        ((nary.reverseRec cons (cons x xs) l) (nary.reverseRec cons xs (nary.append cons x l)))
    )
)

; reverse cons nil xs
; Reverses the list `xs`.
(program nary.reverse
    ((L Type) (cons (-> L L L)) (nil L) (xs L :list))
    ((-> L L L) L L) L
    (
        ((nary.reverse cons nil xs) (nary.reverseRec cons xs nil))
    )
)

; nary.elim cons x
; Returns the sole element if `xs` is a singleton list.
(program nary.elim
    ((L Type) (cons (-> L L L)) (nil L) (c L) (x L) (xs L :list))
    ((-> L L L) L L L) L
    (
        ((nary.elim cons nil c nil) c)
        ((nary.elim cons nil c (cons x nil)) x)
        ((nary.elim cons nil c (cons x xs)) (nary.append cons x xs))
        ((nary.elim cons nil c xs) xs)
    )
)

; nary.intro cons x
; Returns a singleton list if `x` is not a list.
(program nary.intro
    ((L Type) (cons (-> L L L)) (nil L) (x L) (xs L :list))
    ((-> L L L) L L) L
    (
        ((nary.intro cons nil (cons x xs)) (nary.append cons x xs))
        ((nary.intro cons nil x)           (nary.append cons x nil))
    )
)


; nary.at cons i xs
; I should be a numeral
(program nary.at
    ((L Type) (I Type) (cons (-> L L L)) (i I) (x L) (xs L :list))
    ((-> L L L) I L) L
    (
        ((nary.at cons 0 (cons x xs)) x)
        ((nary.at cons i (cons x xs)) (nary.at cons (alf.add i (alf.neg 1)) xs))
    )
)


; nary.is_prefix cons t s
; Retuns `true` if t is a prefix of s
(program nary.is_prefix
    ((L Type) (cons (-> L L L)) (t L) (c1 L) (c2 L) (xs1 L :list) (xs2 L :list))
    ((-> L L L) L L) Bool
    (
        ((nary.is_prefix cons (alf.nil L) t)               true)
        ((nary.is_prefix cons (cons c1 xs1) (cons c2 xs2)) (alf.ite (alf.is_eq c1 c2) (nary.is_prefix cons xs1 xs2) false))
    )
)
