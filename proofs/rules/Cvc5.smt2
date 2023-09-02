; Meta-inclusion for cvc5 rules and extra rules

(include "./Builtin.smt2")
(include "./Booleans.smt2")
(include "../theories/Arrays.smt2")
(include "./Uf.smt2")
(include "./Arith.smt2")
(include "../theories/Transcendentals.smt2")
(include "../theories/BitVectors.smt2")
(include "./Strings.smt2")
(include "../theories/Sets.smt2")


; skolems
;INPUT_VARIABLE
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
(program run_evaluate ((T Type) (S Type) 
                       (x T) (y T) (z S) 
                       (b Bool) (n Int) (m Int))
    (S) S
    (
      ; core
      ((run_evaluate (= x y))      (alf.is_eq (run_evaluate x) (run_evaluate y)))
      ((run_evaluate (ite b x y))  (alf.ite (run_evaluate b) (run_evaluate x) (run_evaluate y)))
  
      ; arithmetic
      ((run_evaluate (< x z))      (alf.is_neg (run_evaluate (- x z))))
      ((run_evaluate (<= x z))     (let ((d (run_evaluate (- x z))))
                                    (alf.or (alf.is_neg d) (alf.is_zero d))))
      ((run_evaluate (> x z))      (alf.is_neg (run_evaluate (- z x))))
      ((run_evaluate (>= x z))     (let ((d (run_evaluate (- z x))))
                                     (alf.or (alf.is_neg d) (alf.is_zero d))))
      ((run_evaluate (+ x z))      (alf.add (run_evaluate x) (run_evaluate z)))
      ((run_evaluate (- x z))      (alf.add (run_evaluate x) (alf.neg (run_evaluate z))))
      ((run_evaluate (* x z))      (alf.mul (run_evaluate x) (run_evaluate z)))
      ((run_evaluate (u- x))       (alf.neg (run_evaluate x)))

      ; strings
      ((run_evaluate (str.++ x y)) (alf.concat (run_evaluate x) (run_evaluate y)))
      ((run_evaluate (str.len x))  (alf.len (run_evaluate x)))
      ((run_evaluate 
         (str.substr x n m))       (alf.extract (run_evaluate n) 
                                      (alf.add (run_evaluate n) (run_evaluate m)) 
                                      (run_evaluate x)))
      ((run_evaluate z)            z)
    )
)

(declare-rule evaluate ((U Type) (t U))
  :args (t)
  :conclusion (= t (run_evaluate t)))
