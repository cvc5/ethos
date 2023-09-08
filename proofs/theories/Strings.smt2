(include "../theories/Builtin.smt2")
(include "../theories/Arith.smt2")

(declare-sort RegLan 0)
(declare-type Seq (Type))
(declare-sort Char 0)
(define-fun String () Type (Seq Char))

(declare-consts <string> String)

; core
(declare-const str.len 
  (-> (! Type :var T :implicit)
      (Seq T) Int))
(declare-const str.++
  (-> (! Type :var T :implicit)
      (Seq T) (Seq T) (Seq T)) :right-assoc-nil)

; extended functions
(declare-const str.substr (-> (! Type :var T :implicit)
                              (Seq T) Int Int (Seq T)))
(declare-const str.contains (-> (! Type :var T :implicit)
                                (Seq T) (Seq T) Bool))
(declare-const str.replace (-> (! Type :var T :implicit)
                               (Seq T) (Seq T) (Seq T) (Seq T)))
(declare-const str.indexof (-> (! Type :var T :implicit)
                               (Seq T) (Seq T) Int Int))
(declare-const str.at (-> (! Type :var T :implicit)
                          (Seq T) Int (Seq T)))
(declare-const str.prefixof (-> (! Type :var T :implicit)
                                (Seq T) (Seq T) Bool))
(declare-const str.suffixof (-> (! Type :var T :implicit)
                                (Seq T) (Seq T) Bool))
(declare-const str.rev (-> (! Type :var T :implicit)
                           (Seq T) (Seq T)))
(declare-const str.unit (-> Int String))
(declare-const str.update (-> (! Type :var T :implicit)
                              (Seq T) Int (Seq T) (Seq T)))
(declare-const str.to_lower (-> String String))
(declare-const str.to_upper (-> String String))
(declare-const str.to_code (-> String Int))
(declare-const str.from_code (-> Int String))
(declare-const str.is_digit (-> String Bool))
(declare-const str.to_int (-> String Int))
(declare-const str.from_int (-> Int String))
(declare-const str.< (-> String String Bool))
(declare-const str.<= (-> String String Bool))
(declare-const str.replace_all (-> (! Type :var T :implicit)
                                   (Seq T) (Seq T) (Seq T) (Seq T)))
(declare-const str.replace_re (-> String RegLan String String))
(declare-const str.replace_re_all (-> String RegLan String String))
(declare-const str.indexof_re (-> String RegLan Int Int))

; regular expressions
(declare-const re.allchar RegLan)
(declare-const re.none RegLan)
(declare-const re.all RegLan)
(declare-const re.empty RegLan)
(declare-const str.to_re (-> String RegLan))
(declare-const re.* (-> RegLan RegLan))
(declare-const re.+ (-> RegLan RegLan))
(declare-const re.opt (-> RegLan RegLan))
(declare-const re.comp (-> RegLan RegLan))
(declare-const re.range (-> String String RegLan))
(declare-const re.++ (-> RegLan RegLan RegLan) :right-assoc-nil)
(declare-const re.inter (-> RegLan RegLan RegLan) :right-assoc-nil)
(declare-const re.union (-> RegLan RegLan RegLan) :right-assoc-nil)
(declare-const re.diff (-> RegLan RegLan RegLan))
(declare-const re.loop (-> Int Int RegLan RegLan))
(declare-const str.in_re (-> String RegLan Bool))


; Sequences
(declare-const seq.empty (-> (! Type :var T) T))
(declare-const seq.unit (-> (! Type :var T :implicit) T (Seq T)))
(declare-const seq.nth (-> (! Type :var T :implicit) (Seq T) Int (alf.ite (alf.is_eq T Char) Int T)))
(declare-const seq.len (-> (! Type :var T :implicit) (Seq T) Int))

; sequence operators just convert to the string operators
(define seq.++ () str.++)
(define seq.extract () str.substr)
(define seq.contains () str.contains)
(define seq.replace () str.replace)
(define seq.indexof () str.indexof)
(define seq.prefixof () str.prefixof)
(define seq.suffixof () str.suffixof)
(define seq.rev () str.rev)
(define seq.update () str.update)

; skolems
(declare-const @k.RE_UNFOLD_POS_COMPONENT (-> String RegLan Int String))
(declare-const @k.STRINGS_DEQ_DIFF (-> (! Type :var T :implicit) (Seq T) (Seq T) Int))
(declare-const @k.STRINGS_STOI_RESULT (-> String Int Int))
(declare-const @k.STRINGS_STOI_NON_DIGIT (-> String Int))
(declare-const @k.STRINGS_ITOS_RESULT (-> Int Int Int))

(declare-const @k.STRINGS_NUM_OCCUR (-> (! Type :var T :implicit) (Seq T) (Seq T) Int))
(declare-const @k.STRINGS_NUM_OCCUR_RE (-> String RegLan Int))
(declare-const @k.STRINGS_OCCUR_INDEX (-> (! Type :var T :implicit) (Seq T) (Seq T) Int Int))
(declare-const @k.STRINGS_OCCUR_INDEX_RE (-> String RegLan Int Int))
(declare-const @k.STRINGS_OCCUR_LEN (-> (! Type :var T :implicit) (Seq T) (Seq T) Int Int))
(declare-const @k.STRINGS_OCCUR_LEN_RE (-> String RegLan Int Int))

(declare-const @k.STRINGS_REPLACE_ALL_RESULT (-> (! Type :var T :implicit) (Seq T) Int (Seq T)))

(declare-const @k.RE_FIRST_MATCH_PRE (-> String RegLan String))
(declare-const @k.RE_FIRST_MATCH (-> String RegLan String))
(declare-const @k.RE_FIRST_MATCH_POST (-> String RegLan String))


