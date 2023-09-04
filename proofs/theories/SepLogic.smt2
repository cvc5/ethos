
(declare-const sep.nil (-> (! Type :var T) T))
(declare-const sep.emp Bool)



(define sep (# x term (# y term (apply (apply f_sep x) y))))
(declare f_sep_label term)
(define sep_label (# x term (# y term (apply (apply f_sep_label x) y))))
(declare f_wand term)
(define wand (# x term (# y term (apply (apply f_wand x) y))))
(declare f_pto term)
(define pto (# x term (# y term (apply (apply f_pto x) y))))
; the empty heap constraint
(declare sep.emp term)
; internally generated in separation logic reductions
(declare f_SEP_LABEL term)
(define SEP_LABEL (# x term (# y term (apply (apply f_SEP_LABEL x) y))))
