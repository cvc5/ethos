(include "../theories/Core.smt2")
(include "../programs/Nary.smt2")

; SPLIT
(declare-rule split ((F Bool))
    :premises ()
    :args (F)
    :conclusion (or F (not F))
)

; RESOLUTION
(program resolve ((C1 Bool) (C2 Bool) (pol Bool) (L Bool))
    (Bool Bool Bool Bool) Bool
    (
        ; Both "clauses" are just the literal
        ((resolve C1 (not C1) true  C1) false)
        ((resolve (not C1) C1 false C1) false)
        ; The first "clause" is the literal
        ((resolve C1       C2 true  C1) (removeLeft (not C1) C2))
        ((resolve (not C1) C2 false C1) (removeLeft      C1  C2))
        ; The second "clause" is the literal
        ((resolve C1 (not C2) true  C2) (removeLeft      C2  C1))
        ((resolve C1      C2  false C2) (removeLeft (not C2) C1))
        ; Neither clause is just the literal
        ((resolve C1 C2 true  L) (appendLeft or (removeLeft      L  C1) (removeLeft (not L) C2)))
        ((resolve C1 C2 false L) (appendLeft or (removeLeft (not L) C1) (removeLeft      L  C2)))
    )
)

(declare-rule resolution ((C1 Bool) (C2 Bool) (pol Bool) (L Bool))
    :premises (C1 C2)
    :args (pol L)
    :conclusion (resolve C1 C2 pol L)
)

; CHAIN_RESOLUTION
; MACRO_RESOLUTION_TRUST3
; MACRO_RESOLUTION
; FACTORING
; REORDERING


; EQ_RESOLVE
; MODUS_PONENS
; NOT_NOT_ELIM
; CONTRA
; AND_ELIM
; AND_INTRO
; NOT_OR_ELIM
; IMPLIES_ELIM
; NOT_IMPLIES_ELIM1
; NOT_IMPLIES_ELIM2
; EQUIV_ELIM1
; EQUIV_ELIM2
; NOT_EQUIV_ELIM1
; NOT_EQUIV_ELIM2
; XOR_ELIM1
; XOR_ELIM2
; NOT_XOR_ELIM1
; NOT_XOR_ELIM2
; ITE_ELIM1
; ITE_ELIM2
; NOT_ITE_ELIM1
; NOT_ITE_ELIM2
; NOT_AND
; CNF_AND_POS
; CNF_AND_NEG
; CNF_OR_POS
; CNF_OR_NEG
; CNF_IMPLIES_POS
; CNF_IMPLIES_NEG1
; CNF_IMPLIES_NEG2
; CNF_EQUIV_POS1
; CNF_EQUIV_POS2
; CNF_EQUIV_NEG1
; CNF_EQUIV_NEG2
; CNF_XOR_POS1
; CNF_XOR_POS2
; CNF_XOR_NEG1
; CNF_XOR_NEG2
; CNF_ITE_POS1
; CNF_ITE_POS2
; CNF_ITE_POS3
; CNF_ITE_NEG1
; CNF_ITE_NEG2
; CNF_ITE_NEG3
; SAT_REFUTATION