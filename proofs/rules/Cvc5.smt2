; Meta-inclusion for cvc5 rules and extra rules

(include "./Builtin.smt2")
(include "./Booleans.smt2")
(include "./Uf.smt2")
(include "./Strings.smt2")



; skolems
;INPUT_VARIABLE
;ARRAY_DEQ_DIFF
;DIV_BY_ZERO
;INT_DIV_BY_ZERO
;MOD_BY_ZERO
;SQRT
;TRANSCENDENTAL_PURIFY_ARG
;SHARED_SELECTOR
;QUANTIFIERS_SKOLEMIZE
;QUANTIFIERS_SYNTH_FUN_EMBED
;STRINGS_NUM_OCCUR
;STRINGS_OCCUR_INDEX
;STRINGS_OCCUR_LEN
;STRINGS_DEQ_DIFF
;STRINGS_REPLACE_ALL_RESULT
;STRINGS_ITOS_RESULT
;STRINGS_STOI_RESULT
;STRINGS_STOI_NON_DIGIT
;SK_FIRST_MATCH_PRE
;SK_FIRST_MATCH
;SK_FIRST_MATCH_POST
;RE_UNFOLD_POS_COMPONENT
;SEQ_MODEL_BASE_ELEMENT
;BAGS_CARD_CARDINALITY
;BAGS_CARD_ELEMENTS
;BAGS_CARD_N
;BAGS_CARD_UNION_DISJOINT
;BAGS_CHOOSE
;BAGS_FOLD_CARD
;BAGS_FOLD_COMBINE
;BAGS_FOLD_ELEMENTS
;BAGS_FOLD_UNION_DISJOINT
;BAGS_MAP_PREIMAGE
;BAGS_MAP_PREIMAGE_SIZE
;BAGS_MAP_PREIMAGE_INDEX
;BAGS_MAP_SUM
;BAGS_DEQ_DIFF
;TABLES_GROUP_PART
;TABLES_GROUP_PART_ELEMENT
;RELATIONS_GROUP_PART
;RELATIONS_GROUP_PART_ELEMENT
;SETS_CHOOSE
;SETS_DEQ_DIFF
;SETS_FOLD_CARD
;SETS_FOLD_COMBINE
;SETS_FOLD_ELEMENTS
;SETS_FOLD_UNION
;SETS_MAP_DOWN_ELEMENT
;HO_TYPE_MATCH_PRED
;IEVAL_NONE
;IEVAL_SOME
;ABSTRACT_VALUE
;SYGUS_ANY_CONSTANT

; evaluate, for all theories
(program run_evaluate ((T Type) (U Type) (S Type) (a T) (b U) (z S))
    (S) S
    (
      ((run_evaluate (= a b))  (alf.is_eq (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (< a b))  (alf.is_neg (run_evaluate (- a b))))
      ((run_evaluate (<= a b)) (let ((x (run_evaluate (- a b))))
                                 (alf.or (alf.is_neg x) (alf.is_zero x))))
      ((run_evaluate (> a b))  (alf.is_neg (run_evaluate (- b a))))
      ((run_evaluate (>= a b)) (let ((x (run_evaluate (- b a))))
                                 (alf.or (alf.is_neg x) (alf.is_zero x))))
      ((run_evaluate (+ a b))  (alf.add (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (- a b))  (alf.add (run_evaluate a) (alf.neg (run_evaluate b))))
      ((run_evaluate (* a b))  (alf.mul (run_evaluate a) (run_evaluate b)))
      ((run_evaluate z)        z)
    )
)
