(include "../theories/Core.smt2")
(include "../theories/Arith.smt2")


; A finite field constant is a term having 2 integer children.
(declare-const f_ff.value term)
(define ff.value (# x term (# y term (apply (apply f_ff.value x) y))))
(declare-const f_ff.add term)
(define ff.add (# x term (# y term (apply (apply f_ff.add x) y))))
(declare-const f_ff.neg term)
(define ff.neg (# x term (apply f_ff.neg x)))
(declare-const f_ff.mul term)
(define ff.mul (# x term (# y term (apply (apply f_ff.mul x) y))))
