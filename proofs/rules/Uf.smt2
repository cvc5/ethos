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
; Only binary trans supported
(declare-rule trans ((T Type) (t1 T) (t2 T) (t3 T))
    :premises ((= t1 t2) (= t2 t3))
    :args ()
    :conclusion (= t1 t3)
)

; CONG
(program mk_cong_eq ((T Type) (U Type) (f1 (-> T U)) (f2 (-> T U)) (t1 U) (t2 U) (tail Bool :list))
    (Bool Bool) Bool
    (
        ((mk_cong_eq (= f1 f2) (alf.nil Bool)) (= f1 f2))
        ((mk_cong_eq (= f1 f2) (= t1 t2)) (= (f1 t1) (f2 t2)))
        ((mk_cong_eq (= f1 f2) (and (= t1 t2) tail)) (mk_cong_eq (= (f1 t1) (f2 t2)) tail))
    )
)

(declare-rule cong ((T Type) (U Type) (E Bool) (f (-> T U)))
    :premise-list E and
    :args (f)
    :conclusion (mk_cong_eq (= f f) E)
)

; N-ary congruence
(program add_nary_arg ((U Type) (f (-> U U)) (s1 U) (s2 U) (t1 U) (t2 U) (nil U :list))
    ((-> U U) U U Bool) Bool
    (
      ((add_nary_arg f s1 s2 (= t1 t2)) (= (f s1 t1) (f s2 t2)))
    )
)

(program mk_nary_cong_eq ((U Type) (f (-> U U)) (t1 U :list) (t2 U :list) (s1 U) (s2 U) (nil U) (tail Bool :list))
    ((-> U U) U Bool) Bool
    (
        ((mk_nary_cong_eq f nil (alf.nil Bool))       (= nil nil))
        ((mk_nary_cong_eq f nil (= s1 s2))            (= s1 s2))
        ((mk_nary_cong_eq f nil (and (= s1 s2) tail)) (add_nary_arg f s1 s2 (mk_nary_cong_eq f nil tail)))
    )
)

(declare-rule nary_cong ((U Type) (E Bool) (f (-> U U)))
    :premise-list E and
    :args (U f)
    :conclusion (mk_nary_cong_eq f (alf.nil U) E)
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
; Only binary ho_cong supported
(declare-rule ho_cong ((T Type) (U Type) (f (-> T U)) (g (-> T U)) (t1 T) (t2 T))
    :premises ((= f g) (= t1 t2))
    :args ()
    :conclusion (= (f t1) (g t2))
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
