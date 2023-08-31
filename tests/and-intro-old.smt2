; AND_INTRO
; Since we don't have premise lists, we implement different variants of and_intro

; Appends F to the head of Fs where Fs is a null-terminated list.
; I.e. `F`, `(and F1 (and F2 .. (and Fn nil)..)` ==>
;    `(and F ( and F1 (and F2 .. (and Fn nil)..)`
(declare-rule and_intro_nary ((F Bool) (Fs Bool))
    :premises (F Fs)
    :conclusion (nary.append and F Fs)
)

; binary and introduction
(declare-rule and_intro ((F1 Bool) (F2 Bool))
    :premises (F1 F2)
    :conclusion (and F1 F2) ; Note: this creates `(and F1 (and F2 nil))`.
)
