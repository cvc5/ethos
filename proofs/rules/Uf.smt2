(include "../theories/Core.smt2")

; REFL
(declare-rule refl ((T Type) (t T))
    :premises ()
    :args (t)
    :conclusion (= t t)
)

; SYMM
; Either t1 = t2 ==> t2 = t1 or t1 != t2 ==> t2 != t1
(program flipEq ((T Type) (t1 T) (t2 T))
    (Bool) Bool
    (
        ((flipEq (= t1 t2)) (= t2 t1))
        ((flipEq (not (= t1 t2))) (not (= t2 t1)))
    )
)

(declare-rule symm ((F Bool))
    :premises (F)
    :args ()
    :conclusion (flipEq F)
)

; TRANS
; note that we assume that there is never exactly one premise
(program mk_trans ((U Type) (t1 U) (t2 U) (t3 U) (t4 U) (tail Bool :list))
    (U U Bool) Bool
    (
        ((mk_trans t1 t2 (and (= t3 t4) tail))
            (alf.ite (alf.is_eq t2 t3) (mk_trans t1 t4 tail) alf.fail))
        ((mk_trans t1 t2 alf.nil)              (= t1 t2))
    )
)

(declare-rule trans ((T Type) (U Type) (E Bool) (f (-> T U)))
    :premise-list E and
    :conclusion
        (alf.match ((t1 U) (t2 U) (tail Bool :list))
        E
        ((and (= t1 t2) tail) (mk_trans t1 t2 tail)))
)

; CONG
(program mk_cong ((T Type) (U Type) (f1 (-> T U)) (f2 (-> T U)) (t1 U) (t2 U) (tail Bool :list))
    (U U Bool) Bool
    (
        ((mk_cong f1 f2 (and (= t1 t2) tail)) (mk_cong (f1 t1) (f2 t2) tail))
        ((mk_cong t1 t2 alf.nil)              (= t1 t2))
        ((mk_cong f1 f2 (= t1 t2))            (= (f1 t1) (f2 t2)))
    )
)

(declare-rule cong ((T Type) (U Type) (E Bool) (f (-> T U)))
    :premise-list E and
    :args (f)
    :conclusion (mk_cong f f E)
)

; N-ary congruence
; note that arguments are provided in reverse order to avoid intermediate node construction
(program mk_nary_cong ((U Type) (f (-> U U)) (t1 U) (t2 U) (s1 U) (s2 U) (tail Bool :list))
    ((-> U U) U U Bool) Bool
    (
        ((mk_nary_cong f t1 t2 (and (= s1 s2) tail)) (mk_nary_cong f (f s1 t1) (f s2 t2) tail))
        ((mk_nary_cong f t1 t2 alf.nil)              (= t1 t2))
    )
)

(declare-rule nary_cong ((U Type) (E Bool) (f (-> U U)))
    :premise-list E and
    :args (f)
    :conclusion (mk_nary_cong f alf.nil alf.nil E)
)

; TRUE_INTRO
(declare-rule true_intro ((F Bool))
    :premises (F)
    :args ()
    :conclusion (= F true)
)

; TRUE_ELIM
(declare-rule true_elim ((F Bool))
    :premises ((= F true))
    :args ()
    :conclusion F
)

; FALSE_INTRO
(declare-rule false_intro ((F Bool))
    :premises ((not F))
    :args ()
    :conclusion (= F false)
)

; FALSE_ELIM
(declare-rule false_elim ((F Bool))
    :premises ((= F false))
    :args ()
    :conclusion (not F)
)


; HO_CONG
(program mk_ho_cong ((T Type) (U Type) (f1 (-> T U)) (f2 (-> T U)) (t1 U) (t2 U) (tail Bool :list))
    (U U Bool) Bool
    (
        ((mk_ho_cong f1 f2 (and (= t1 t2) tail)) (mk_ho_cong (f1 t1) (f2 t2) tail))
        ((mk_ho_cong t1 t2 alf.nil)              (= t1 t2))
    )
)

(declare-rule ho_cong ((T Type) (U Type) (E Bool) (f (-> T U)))
    :premise-list E and
    :args ()
    :conclusion
        (alf.match ((t1 U) (t2 U) (tail Bool :list))
        E
        ((and (= t1 t2) tail) (mk_ho_cong t1 t2 tail)))
)

; HO_APP_ENCODE
; TO TRUST: t_encoded is the result of the applicative encoding.
(declare-rule ho_app_encode ((T Type) (t T) (t_encoded T))
    :premises ()
    :args (t t_encoded)
    :conclusion (= t t_encoded)
)

; BETA_REDUCE
; TODO
