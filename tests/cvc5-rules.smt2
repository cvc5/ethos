; Experimental rules for the internal cvc5 rules.

(declare-sort Int 0)

(declare-const = (-> (! Type :var T) T T Bool))

(declare-const and (-> Bool Bool Bool))
(declare-const or (-> Bool Bool Bool))
(declare-const not (-> Bool Bool))
(declare-const => (-> Bool Bool Bool))
(declare-const false Bool)

; ASSUME
; SCOPE

; SUBS
(declare-rule subs ((T Type) (F Bool :list) (t1 T) (t2 T) (ids Int :list))
    :premises (F)
    :args (t1 ids)
    :conclusion (= T t1 t2)
    :require ((t2) (= T t2 (Subst t F ids)))
)

; REWRITE
(declare-rule rewrite ((T Type) (t1 T) (t2 T) (idr Int))
    :args (t1 idr)
    :conclusion (= T t1 t2)
    :require ((t2) (= T t2 (Rewriter idr t)))
)

; EVALUATE
(declare-rule evaluate ((T Type) (t1 T) (t2 T))
    :args (t1)
    :conclusion (= T t1 t2)
    :require ((t2) (Evaluate idr t))
)

; MACRO_SR_EQ_INTRO
(declare-rule marco_sr_eq_intro ((T Type) (F Bool :list) (t1 T) (t2 T) (idsar Int :list))
    :premises (F)
    :args (t1 idsar) ; We have to merge the three arguments since they are all Int
    :conclusion t2
    :require (= T t2 (RwSubstSk t1 F idsar))
)

; MACRO_SR_PRED_INTRO
(declare-rule marco_sr_eq_intro ((T Type) (F Bool :list) (R Bool) (idsar Int :list))
    :premises (F)
    :args (R idsar) ; We have to merge the three arguments since they are all Int
    :conclusion R
)

; MACRO_SR_PRED_ELIM
(declare-rule marco_sr_pred_elim ((T Type) (F Bool :list) (R Bool) (C Bool) (idsar Int :list))
    :premises (R F)
    :args (idsar) ; We have to merge the three arguments since they are all Int
    :conclusion C
    :require ((C) (= T C (RwSubstSk R F idsar)))
)

; MACRO_SR_PRED_TRANSFORM
(declare-rule marco_sr_pred_transform ((T Type) (F Bool :list) (R Bool) (G Bool) (idsar Int :list))
    :premises (R F)
    :args (G idsar) ; We have to merge the three arguments since they are all Int
    :conclusion G
)

; ANNOTATION
(declare-rule annotation ((F Bool) (a Int :list))
    :premises (F)
    :args (a)
    :conclusion F
)

; REMOVE_TERM_FORMULA_AXIOM
(declare-rule remove_term_formula_axiom ((T Type) (t T) (C Bool))
    :args (t)
    :conclusion C
    :require ((C) (= T C RemoveTermFormulas_getAxiomFor t))
)

; THEORY_LEMMA
(declare-rule theory_lemma ((F Bool) (tid Int))
    :conclusion F
)

; THEORY_REWRITE
(declare-rule theory_rewrite ((F Bool) (tid Int) (rid Int))
    :args (tid rid)
    :conclusion F
)

; Some of those might have more structure that can be gleaned from
; their textual description, but we ignore this for now.
; THEORY_PREPROCESS
; THEORY_PREPROCESS_LEMMA
; PREPROCESS
; PREPROCESS_LEMMA
; THEORY_EXPAND_DEF
; WITNESS_AXIOM
; TRUST_REWRITE
; TRUST_FLATTENING_REWRITE
; TRUST_SUBS
; TRUST_SUBS_MAP
(declare-rule theory_preprocess ((F Bool))
    :conclusion F
)
(declare-rule theory_preprocess_lemma ((F Bool))
    :conclusion F
)
(declare-rule preprocess ((F Bool))
    :conclusion F
)
(declare-rule preprocess_lemma ((F Bool))
    :conclusion F
)
(declare-rule theory_expand_def ((F Bool))
    :conclusion F
)
(declare-rule witness_axiom ((F Bool))
    :conclusion F
)
(declare-rule trust_rewrite ((F Bool))
    :conclusion F
)
(declare-rule trust_flattening_rewrite ((F Bool))
    :conclusion F
)
(declare-rule trust_subs ((F Bool))
    :premises ()
    :args ()
    :conclusion F
)
(declare-rule trust_subs_map ((F Bool))
    :conclusion F
)

; TRUST_SUBS_EQ
(declare-rule trust_subs_eq ((Fp Bool) (F Bool))
    :premises (Fp)
    :conclusion F
)

; THEORY_INFERENCE
(declare-rule theory_inference ((F Bool))
    :conclusion F
)

; SAT_REFUTATION
(declare-rule sat_refutation ((F1 Bool) (F Bool :list))
    :args (F1 F)
    :conclusion false
)

; RESOLUTION
(declare-rule resolution ((C1 Bool) (C2 Bool) (C Bool) (pol Bool) (L Bool))
    :premises (C1 C2)
    :args (pol L)
    :conclusion C
    :require ((C) (= T C resolve C1 C2 pol L))
)

; CHAIN_RESOLUTION
(declare-rule chain_resolution ((Cs Bool :list) (C Bool) (polandlits Bool :list))
    :premises (Cs)
    :args (polandlits)
    :conclusion C
    :require ((C) (= T C (chainresolve C polandlits)))
)

; FACTORING
(declare-rule factoring ((C1 Bool) (C2 Bool))
    :premises (C1)
    :conclusion C2
    :require ((C2) (= T C2 (factor C1)))
)

; REORDERING
(declare-rule reordering ((C1 Bool) (C2 Bool))
    :premises (C1)
    :conclusion C2
    :require ((C2) (isPermutation C1 C2)) 
)

; MACRO_RESOLUTION
(declare-rule macro_resolution ((Cs Bool :list) (C Bool) (polandlits Bool :list))
    :premises (Cs)
    :args (C polandlits)
    :conclusion C
    :require ((C) (= T C (macroresolve C polandlits)))
)

; MACRO_RESOLUTION_TRUST
(declare-rule macro_resolution_trust ((Cs Bool :list) (C Bool) (polandlits Bool :list))
    :premises (Cs)
    :args (C polandlits)
    :conclusion C
    :require ((C) (= T C (macroresolve C polandlits)))
)

; SPLIT
(declare-rule split ((F Bool))
    :args (F)
    :conclusion (or F (not F))
)

; EQ_RESOLVE
(declare-rule eq_resolve ((F1 Bool) (F2 Bool))
    :premises (F1 (= Bool F1 F2))
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
(declare-rule and_elim ((F1 Bool) (Fs Bool :list) (Fi Bool) (i Int))
    :premises ((and F1 Fs))
    :args (i)
    :conclusion Fi
    :require (= Fi (select i (cons F1 Fs)))
)

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
; REFL
; SYMM
; TRANS
; CONG
; TRUE_INTRO
; TRUE_ELIM
; FALSE_INTRO
; FALSE_ELIM
; HO_APP_ENCODE
; HO_CONG
; BETA_REDUCE
; ARRAYS_READ_OVER_WRITE
; ARRAYS_READ_OVER_WRITE_CONTRA
; ARRAYS_READ_OVER_WRITE_1
; ARRAYS_EXT
; ARRAYS_EQ_RANGE_EXPAND
; BV_BITBLAST
; BV_BITBLAST_STEP
; BV_EAGER_ATOM
; DT_UNIF
; DT_INST
; DT_COLLAPSE
; DT_SPLIT
; DT_CLASH
; SKOLEM_INTRO
; SKOLEMIZE
; INSTANTIATE
; ALPHA_EQUIV
; QUANTIFIERS_PREPROCESS
; CONCAT_EQ
; CONCAT_UNIFY
; CONCAT_CONFLICT
; CONCAT_SPLIT
; CONCAT_CSPLIT
; CONCAT_LPROP
; CONCAT_CPROP
; STRING_DECOMPOSE
; STRING_LENGTH_POS
; STRING_LENGTH_NON_EMPTY
; STRING_REDUCTION
; STRING_EAGER_REDUCTION
; RE_INTER
; RE_UNFOLD_POS
; RE_UNFOLD_NEG
; RE_UNFOLD_NEG_CONCAT_FIXED
; RE_ELIM
; STRING_CODE_INJ
; STRING_SEQ_UNIT_INJ
; STRING_INFERENCE
; MACRO_ARITH_SCALE_SUM_UB
; ARITH_SUM_UB
; INT_TIGHT_UB
; INT_TIGHT_LB
; ARITH_TRICHOTOMY
; ARITH_OP_ELIM_AXIOM
; ARITH_POLY_NORM
; ARITH_MULT_SIGN
; ARITH_MULT_POS
; ARITH_MULT_NEG
; ARITH_MULT_TANGENT
; ARITH_TRANS_PI
; ARITH_TRANS_EXP_NEG
; ARITH_TRANS_EXP_POSITIVITY
; ARITH_TRANS_EXP_SUPER_LIN
; ARITH_TRANS_EXP_ZERO
; ARITH_TRANS_EXP_APPROX_ABOVE_NEG
; ARITH_TRANS_EXP_APPROX_ABOVE_POS
; ARITH_TRANS_EXP_APPROX_BELOW
; ARITH_TRANS_SINE_BOUNDS
; ARITH_TRANS_SINE_SHIFT
; ARITH_TRANS_SINE_SYMMETRY
; ARITH_TRANS_SINE_TANGENT_ZERO
; ARITH_TRANS_SINE_TANGENT_PI
; ARITH_TRANS_SINE_APPROX_ABOVE_NEG
; ARITH_TRANS_SINE_APPROX_ABOVE_POS
; ARITH_TRANS_SINE_APPROX_BELOW_NEG
; ARITH_TRANS_SINE_APPROX_BELOW_POS
; ARITH_NL_COVERING_DIRECT
; ARITH_NL_COVERING_RECURSIVE
