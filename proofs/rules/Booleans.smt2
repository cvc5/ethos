(include "../theories/Core.smt2")
(include "../theories/Ints.smt2")

(include "../programs/Nary.smt2")

; SCOPE

(declare-rule scope
  ((F Bool) (G Bool))
  :assumption F
  :premises (G)
  :args ()
  :conclusion (=> F G)
)

(program extract_antec
   ((C Bool) (F1 Bool) (F2 Bool))
   (Bool Bool) Bool
   (
   ((extract_antec C C) (alf.nil Bool))
   ((extract_antec (=> F1 F2) C) (nary.append and F1 (extract_antec F2 C)))
   )
)

(program run_process_scope
   ((C Bool) (F Bool))
   (Bool Bool) Bool
   (
   ((run_process_scope F false) (not (nary.elim and (extract_antec F false))))
   ((run_process_scope F C) (=> (nary.elim and (extract_antec F C)) C))
   )
)

; this rule processes the result of n scopes into the conclusion expected by PfRule::SCOPE
(declare-rule process_scope
  ((C Bool) (F Bool))
  :premises (F)
  :args (C)
  :conclusion (run_process_scope F C)
)

; SPLIT
(declare-rule split ((F Bool))
    :premises ()
    :args (F)
    :conclusion (or F (not F))
)

; Extension of `nary.remove or l C`, that returns `false` if `C` is `l`
(program removeSelf ((l Bool) (C Bool))
    (Bool Bool) Bool
    (
        ((removeSelf l l) false)
        ((removeSelf l C) (nary.remove or l C))
    )
)

; RESOLUTION
(program resolve ((C1 Bool) (C2 Bool) (pol Bool) (L Bool))
    (Bool Bool Bool Bool) Bool
    (
        ((resolve C1 C2 true  L)
          (nary.elim or (alf.nil Bool) false (nary.concat or
            (removeSelf      L  (nary.intro or (alf.nil Bool) C1)) (removeSelf (not L) (nary.intro or (alf.nil Bool) C2)))))
        ((resolve C1 C2 false L)
          (nary.elim or (alf.nil Bool) false (nary.concat or
            (removeSelf (not L) (nary.intro or (alf.nil Bool) C1)) (removeSelf      L  (nary.intro or (alf.nil Bool) C2)))))
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
        ((chainResolveRec C1 (alf.nil Bool) (alf.nil Bool)) C1)
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
; TODO: use generic lists for `args` instead of a conjunction.
(declare-rule chain_resolution ((Cs Bool) (args Bool))
    :premises (Cs)
    :args (args)
    :conclusion (chainResolve Cs args)
)

; MACRO_RESOLUTION_TRUST
; MACRO_RESOLUTION
; These rules do not perform any checks.
; TODO: implement some checking for MACRO_RESOLUTION
(declare-rule macro_resolution_trust((C Bool) (Cs Bool) (args Bool))
    :premises (Cs)
    :args (C args)
    :conclusion C
)
(declare-rule macro_resolution((C Bool) (Cs Bool) (args Bool))
    :premises (Cs)
    :args (C args)
    :conclusion C
)

; FACTORING
; factorLiterals xs x returns x with duplicates removed, xs is a list of
; literals we have seen before.
(program factorLiterals ((xs Bool :list) (l Bool) (ls Bool :list))
    (Bool Bool) Bool
    (
        ((factorLiterals xs (alf.nil Bool)) (alf.nil Bool))
        ((factorLiterals xs (or l ls)) (let ((cond (nary.ctn or l xs)))
                                       (let ((ret (factorLiterals
                                                    (alf.ite cond xs (nary.append or l xs))
                                                    ls)))
                                            (alf.ite cond ret (nary.append or l ret)))))
    )
)

(declare-rule factoring ((C Bool))
    :premises (C)
    :conclusion (nary.elim or (alf.nil Bool) false (factorLiterals (alf.nil Bool) C))
)

(declare-rule reordering ((C1 Bool) (C2 Bool))
    :premises (C1)
    :args (C2)
    :requires (((nary.is_subset or C1 C2) true))
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

; AND_ELIM
(declare-rule and_elim ((Fs Bool) (i Int))
    :premises (Fs)
    :args (i)
    :conclusion (nary.at and i Fs)
)

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

; NOT_OR_ELIM
(declare-rule not_or_elim ((Fs Bool) (i Int))
    :premises ((not Fs))
    :args (i)
    :conclusion (not (nary.at or i Fs))
)

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

; lowerNotAnd c
; Moves a negation into a disjunction.
; `lowerNotAnd (and l1 .. ln) = (or (not l1) ... (not ln))`
(program lowerNotAnd ((l Bool) (ls Bool :list))
    (Bool) Bool
    (
        ((lowerNotAnd (alf.nil Bool)) (alf.nil Bool)) ; Terminator changes
        ((lowerNotAnd (and l ls)) (nary.append or (not l) (lowerNotAnd ls)))
    )
)

(declare-rule not_and ((F Bool))
    :premises ((not F))
    :conclusion (lowerNotAnd F)
)

; CNF_AND_POS
(declare-rule cnf_and_pos ((Fs Bool) (i Int))
    :args (Fs i)
    :conclusion (or (not Fs) (nary.at and i Fs))
)

; CNF_AND_NEG
(declare-rule cnf_and_neg ((Fs Bool))
    :args (Fs)
    :conclusion (nary.append or Fs (lowerNotAnd Fs))
)

; CNF_OR_POS
(declare-rule cnf_or_pos ((Fs Bool))
    :args (Fs)
    :conclusion (nary.append or (not Fs) Fs)
)

; CNF_OR_NEG
(declare-rule cnf_or_neg ((Fs Bool) (i Int))
    :args (Fs i)
    :conclusion (nary.concat or Fs (nary.append or (not (nary.at or i Fs)) (alf.nil Bool)))
)

; CNF_IMPLIES_POS
(declare-rule cnf_implies_pos ((F1 Bool) (F2 Bool))
    :args ((=> F1 F2))
    :conclusion (or (not (=> F1 F2)) (not F1) F2)
)

; CNF_IMPLIES_NEG1
(declare-rule cnf_implies_neg1 ((F1 Bool) (F2 Bool))
    :args ((=> F1 F2))
    :conclusion (or (=> F1 F2) F1)
)

; CNF_IMPLIES_NEG2
(declare-rule cnf_implies_neg2 ((F1 Bool) (F2 Bool))
    :args ((=> F1 F2))
    :conclusion (or (=> F1 F2) (not F2))
)

; CNF_EQUIV_POS1
(declare-rule cnf_equiv_pos1 ((F1 Bool) (F2 Bool))
    :args ((= F1 F2))
    :conclusion (or (not (= F1 F2)) (not F1) F2)
)

; CNF_EQUIV_POS2
(declare-rule cnf_equiv_pos2 ((F1 Bool) (F2 Bool))
    :args ((= F1 F2))
    :conclusion (or (not (= F1 F2)) F1 (not F2))
)

; CNF_EQUIV_NEG1
(declare-rule cnf_equiv_neg1 ((F1 Bool) (F2 Bool))
    :args ((= F1 F2))
    :conclusion (or (= F1 F2) F1 F2)
)

; CNF_EQUIV_NEG2
(declare-rule cnf_equiv_neg2 ((F1 Bool) (F2 Bool))
    :args ((= F1 F2))
    :conclusion (or (= F1 F2) (not F1) (not F2))
)

; CNF_XOR_POS1
(declare-rule cnf_xor_pos1 ((F1 Bool) (F2 Bool))
    :args ((xor F1 F2))
    :conclusion (or (not (xor F1 F2)) F1 F2)
)

; CNF_XOR_POS2
(declare-rule cnf_xor_pos2 ((F1 Bool) (F2 Bool))
    :args ((xor F1 F2))
    :conclusion (or (not (xor F1 F2)) (not F1) (not F2))
)

; CNF_XOR_NEG1
(declare-rule cnf_xor_neg1 ((F1 Bool) (F2 Bool))
    :args ((xor F1 F2))
    :conclusion (or (xor F1 F2) (not F1) F2)
)

; CNF_XOR_NEG2
(declare-rule cnf_xor_neg2 ((F1 Bool) (F2 Bool))
    :args ((xor F1 F2))
    :conclusion (or (xor F1 F2) F1 (not F2))
)

; CNF_ITE_POS1
(declare-rule cnf_ite_pos1 ((C Bool) (F1 Bool) (F2 Bool))
    :args ((ite C F1 F2))
    :conclusion (or (not (ite C F1 F2)) (not C) F1)
)

; CNF_ITE_POS2
(declare-rule cnf_ite_pos2 ((C Bool) (F1 Bool) (F2 Bool))
    :args ((ite C F1 F2))
    :conclusion (or (not (ite C F1 F2)) C F2)
)

; CNF_ITE_POS3
(declare-rule cnf_ite_pos3 ((C Bool) (F1 Bool) (F2 Bool))
    :args ((ite C F1 F2))
    :conclusion (or (not (ite C F1 F2)) F1 F2)
)

; CNF_ITE_NEG1
(declare-rule cnf_ite_neg1 ((C Bool) (F1 Bool) (F2 Bool))
    :args ((ite C F1 F2))
    :conclusion (or (ite C F1 F2) (not C) (not F1))
)

; CNF_ITE_NEG2
(declare-rule cnf_ite_neg2 ((C Bool) (F1 Bool) (F2 Bool))
    :args ((ite C F1 F2))
    :conclusion (or (ite C F1 F2) C (not F2))
)

; CNF_ITE_NEG3
(declare-rule cnf_ite_neg3 ((C Bool) (F1 Bool) (F2 Bool))
    :args ((ite C F1 F2))
    :conclusion (or (ite C F1 F2) (not F1) (not F2))
)

; SAT_REFUTATION
; trust rule
(declare-rule sat_refutation ((Fs Bool))
    :premises (Fs)
    :conclusion false
)
