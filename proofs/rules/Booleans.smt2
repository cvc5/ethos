(include "../theories/Core.smt2")
(include "../programs/Nary.smt2")

; SPLIT
(declare-rule split ((F Bool))
    :premises ()
    :args (F)
    :conclusion (or F (not F))
)

; Extension of `removeOr l C`, that returns `false` if `C` is `l`
(program removeSelf ((l Bool) (C Bool))
    (Bool Bool) Bool
    (
        ((removeSelf l l) false)
        ((removeSelf l C) (removeOr l C))
    )
)

; RESOLUTION
(program resolve ((C1 Bool) (C2 Bool) (pol Bool) (L Bool))
    (Bool Bool Bool Bool) Bool
    (
        ((resolve C1 C2 true  L)
          (naryElimOr (concatOr
            (removeSelf      L  (naryIntroOr C1)) (removeSelf (not L) (naryIntroOr C2)))))
        ((resolve C1 C2 false L)
          (naryElimOr (concatOr
            (removeSelf (not L) (naryIntroOr C1)) (removeSelf      L  (naryIntroOr C2)))))
    )
)

(declare-rule resolution ((C1 Bool) (C2 Bool) (pol Bool) (L Bool))
    :premises (C1 C2)
    :args (pol L)
    :conclusion (resolve C1 C2 pol L)
)

; CHAIN_RESOLUTION
(program chainResolveRec((C1 Bool) (C2 Bool) (Cs Bool :list) (pol Bool) (L Bool) (args Bool :list))
    (Bool Bool Bool) Bool
    (
        ((chainResolveRec C1 true true) C1)
        ((chainResolveRec C1 (and C2 Cs) (and pol L args)) (chainResolveRec (resolve C1 C2 pol L) Cs args))
    )
)

(program chainResolve((C1 Bool) (Cs Bool :list) (args Bool))
    (Bool Bool) Bool
    (
        ((chainResolve (and C1 Cs) args) (chainResolveRec C1 Cs args))
    )
)

; This is a chain or resolution steps as described in the cvc5 proof rule
; documentation.
; `Cs` is a conjunction or the premise clauses.  This can be built by using
;      multiple `and_intro` steps.
; `args` is a conjunction where the alternating conjuncts are polarity and
;        pivot literal.
(declare-rule chain_resolution ((Cs Bool) (args Bool))
    :premises (Cs)
    :args (args)
    :conclusion (chainResolve Cs args)
)

; MACRO_RESOLUTION_TRUST
; MACRO_RESOLUTION

; FACTORING
(program factorLiterals ((l Bool) (ls Bool :list))
    (Bool) Bool
    (
        ((factorLiterals false) false)
        ((factorLiterals (or l l ls)) (factorLiterals (appendOr l ls)))
        ((factorLiterals (or l ls))   (appendOr l (factorLiterals ls)))
        ((factorLiterals ls) ls)
    )
)

(declare-rule factoring ((C Bool))
    :premises (C)
    :conclusion (factorLiterals C)
)

; REORDERING
; Naive O(n^2) test
(program isPermutation ((l1 Bool) (l2 Bool) (l1s Bool :list) (l2s Bool :list))
    (Bool Bool) Bool
    (
        ((isPermutation l1 l1) true)
        ((isPermutation false l1) false)
        ((isPermutation (or l1 l1s) (or l2 l2s))
          (isPermutation l1s (removeOr l1 (or l2 l2s))))
    )
)

(declare-rule reordering ((C1 Bool) (C2 Bool))
    :premises (C1)
    :args (C2)
    :requires (((isPermutation C1 C2) true))
    :conclusion C2
)

; EQ_RESOLVE
(declare-rule eq_resolve ((F1 Bool) (F2 Bool))
    :premises (F1 (= F1 F2))
    :conclusion F2
)

; MODUS_PONENS
(declare-rule modus_ponens ((F1 Bool) (F2 Bool))
    :premises (F1 (=> F1 F2))
    :conclusion F2
)

; NOT_NOT_ELIM
(declare-rule not_not_elim ((F Bool))
    :premises ((not (not F)))
    :conclusion F
)

; CONTRA
(declare-rule contra ((F Bool))
    :premises (F (not F))
    :conclusion false
)

; TODO: needs integer evaluation
; AND_ELIM

; TODO: needs support for premise lists
; AND_INTRO

; TODO: needs integer evaluation
; NOT_OR_ELIM

; IMPLIES_ELIM
(declare-rule implies_elim ((F1 Bool) (F2 Bool))
    :premises ((=> F1 F2))
    :conclusion (or (not F1) F2)
)

; NOT_IMPLIES_ELIM1
(declare-rule not_implies_elim1 ((F1 Bool) (F2 Bool))
    :premises ((not (=> F1 F2)))
    :conclusion F1
)

; NOT_IMPLIES_ELIM2
(declare-rule not_implies_elim2 ((F1 Bool) (F2 Bool))
    :premises ((not (=> F1 F2)))
    :conclusion (not F2)
)

; EQUIV_ELIM1
(declare-rule equiv_elim1 ((F1 Bool) (F2 Bool))
    :premises ((= F1 F2))
    :conclusion (or (not F1) F2)
)

; EQUIV_ELIM2
(declare-rule equiv_elim2 ((F1 Bool) (F2 Bool))
    :premises ((= F1 F2))
    :conclusion (or F1 (not F2))
)

; NOT_EQUIV_ELIM1
(declare-rule not_equiv_elim1 ((F1 Bool) (F2 Bool))
    :premises ((not (= F1 F2)))
    :conclusion (or F1 F2)
)

; NOT_EQUIV_ELIM2
(declare-rule not_equiv_elim2 ((F1 Bool) (F2 Bool))
    :premises ((not (= F1 F2)))
    :conclusion (or (not F1) (not F2))
)

; XOR_ELIM1
(declare-rule xor_elim1 ((F1 Bool) (F2 Bool))
    :premises ((xor F1 F2))
    :conclusion (or F1 F2)
)

; XOR_ELIM2
(declare-rule xor_elim2 ((F1 Bool) (F2 Bool))
    :premises ((xor F1 F2))
    :conclusion (or (not F1) (not F2))
)

; NOT_XOR_ELIM1
(declare-rule not_xor_elim1 ((F1 Bool) (F2 Bool))
    :premises ((not (xor F1 F2)))
    :conclusion (or F1 (not F2))
)

; NOT_XOR_ELIM2
(declare-rule not_xor_elim2 ((F1 Bool) (F2 Bool))
    :premises ((not (xor F1 F2)))
    :conclusion (or (not F1) F2)
)

; ITE_ELIM1
(declare-rule ite_elim1 ((C Bool) (F1 Bool) (F2 Bool))
    :premises ((ite C F1 F2))
    :conclusion (or (not C) F1)
)

; ITE_ELIM2
(declare-rule ite_elim2 ((C Bool) (F1 Bool) (F2 Bool))
    :premises ((ite C F1 F2))
    :conclusion (or C F2)
)

; NOT_ITE_ELIM1
(declare-rule not_ite_elim1 ((C Bool) (F1 Bool) (F2 Bool))
    :premises ((not (ite C F1 F2)))
    :conclusion (or (not C) (not F1))
)

; NOT_ITE_ELIM2
(declare-rule not_ite_elim2 ((C Bool) (F1 Bool) (F2 Bool))
    :premises ((not (ite C F1 F2)))
    :conclusion (or C (not F2))
)

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
