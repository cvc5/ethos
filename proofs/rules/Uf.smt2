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
; AJR: should just eliminate this and rename ho_cong to cong.
; Only binary cong supported
(declare-rule cong ((T Type) (U Type) (f (-> T U)) (t1 T) (t2 T))
    :premises ((= t1 t2))
    :args (f)
    :conclusion (= (f t1) (f t2))
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
