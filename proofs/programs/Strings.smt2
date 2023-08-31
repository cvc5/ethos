
(include "../theories/Builtin.smt2")
(include "../programs/Nary.smt2")
(include "../theories/Core.smt2")

(include "../theories/Arith.smt2")
(include "../theories/Strings.smt2")


; This signature is used for both strings and sequences, where we often
; write "string" in the documentation to refer to a string or sequence.

; Make empty string of the given string-like sort U.
(program mk_emptystr ((U Type))
  (Type) U
  (
    ((mk_emptystr (Seq U)) (seq.empty (Seq U)))
    ((mk_emptystr String) "")
  )
)

; Return true if s is the empty string or sequence.
(program string_is_empty ((U Type) (x U))
  (U) Bool
  (
    ((string_is_empty (seq.empty U)) true)
    ((string_is_empty "") true)
    ((string_is_empty x) false)
  )
)

;;-------------------- Skolem terms
; The following side conditions are used for computing terms that define
; Skolems, which are used in reductions. Notice that Skolem terms may use
; terms that are not in original form, meaning that the definitions of Skolems
; may themselves contain Skolems. This is to avoid the use of a side condition
; for computing the original form of a term in the LFSC signature, which
; naively is exponential.

; Get the term corresponding to the prefix of term s of fixed length n.
(define-fun skolem_prefix ((U Type) (s U) (n Int)) U
  (str.substr s 0 n)
)

; Get the term corresponding to the suffix of term s of fixed length n.
(define-fun skolem_suffix_rem ((U Type) (s U) (n Int)) U
  (str.substr s n (- (str.len s) n))
)

; Get the term corresponding to the prefix of s before the first occurrence of
; t in s.
(define-fun skolem_first_ctn_pre ((U Type) (s U) (t U)) U
  (skolem_prefix U s (str.indexof s t 0)))

; Get the term corresponding to the suffix of s after the first occurrence of
; t in s.
(define-fun skolem_first_ctn_post ((U Type) (s U) (t U)) U
  (skolem_suffix_rem U s (+ (str.len (skolem (skolem_first_ctn_pre U s t))) (str.len t))))

;;-------------------- Utilities

; Head and tail for string concatenation. Fails if not a concatentation term.
;(program string_head ((t term)) term (nary.head str.++ t))
;(program string_tail ((t term)) term (nary.tail str.++ t))

; Concatenation str.++ applications t1 and t2. Note this side condition requires
; taking the sort u of t1 for constructing the empty string.
(program string_concat ((T Type) (t1 T) (t2 T))
  (T T) T
  (((string_concat t1 t2) (nary.concat str.++ t1 t2)))
)

; Decompose str.++ term t of sort u into a head and tail.
;(program string_decompose ((t term) (u sort)) termPair (nary.decompose str.++ t (mk_emptystr u)))

; String is prefix, returns tt if t1 of sort u is a prefix of t2
;(program string_is_prefix ((t1 term) (t2 term) (u sort)) flag (nary.is_prefix str.++ t1 t2))

; Insert a string into str.++ term t of sort u.
;(program string_insert ((elem term) (t term) (u sort)) term (nary.insert str.++ elem t))

; Return reverse of t if rev = tt, return t unchanged otherwise.
;(program string_rev ((t term) (rev flag) (u sort)) term (ifequal rev tt (nary.reverse str.++ t) t))

; Convert a str.++ application t into its element, if it is a singleton, return t unchanged otherwise.
;(program string_nary.elim ((t term) (u sort)) term (nary.elim str.++ t))

; Convert t into a str.++ application, if it is not already in n-ary form.
;(program string_nary.intro ((t term) (u sort)) term (nary.intro str.++ t))

;;-------------------- Reductions

; In the following, a "reduction predicate" refers to a formula that is used
; to axiomatize an extended string program in terms of (simpler) programs.

; Compute the reduction predicate for (str.substr x n m) of sort U.
(program string_reduction_substr ((U Type) (x U) (n Int) (m Int))
  (U Int Int Type) Bool
  (
    ((string_reduction_substr x n m U)
      (let ((k (skolem (str.substr x n m))))
      (let ((npm (+ n m)))
      (let ((k1 (skolem (skolem_prefix U x n))))
      (let ((k2 (skolem (skolem_suffix_rem U x npm))))
      (ite
        ; condition
        (and (>= n 0)(> (str.len x) n) (> m 0))
        ; if branch
        (and (= x (str.++ k1 k k2))
            (= (str.len k1) n)
            (or (= (str.len k2) (- (str.len x) npm))
                (= (str.len k2) 0))
            (<= (str.len k) m))
        ; else branch
        (= k (mk_emptystr U))
        ))))))
  )
)

; Compute the reduction predicate for (str.indexof x y n) of sort U.
(program string_reduction_indexof ((U Type) (x U) (y U) (n Int))
  (U U Int Type) Bool
  (
    ((string_reduction_indexof x y n U)
      (let ((k (skolem (str.indexof x y n))))
      (let ((xn (str.substr x n (- (str.len x) n))))
      (let ((k1 (skolem (skolem_first_ctn_pre U xn y))))
      (let ((k2 (skolem (skolem_first_ctn_post U xn y))))
      (ite
        (or (not (str.contains xn y)) (> n (str.len x)) (> 0 n))
        (= k (alf.neg 1))
        (ite
          (= y (mk_emptystr U))
          (= k n)
          (and (= xn (str.++ k1 y k2))
              (not (str.contains
                        (str.++ k1 (str.substr y 0 (- (str.len y) 1))) y))
              (= k (+ n (str.len k1)))))))))))
  )
)

; Compute the reduction predicate for term t of sort s. Note that the operators
; listed in comments are missing from the signature currently.
(program string_reduction_pred ((U Type) (x U) (y U) (n Int) (m Int))
  (U Type) Bool
  (
    ((string_reduction_pred (str.substr x n m) U) (string_reduction_substr x n m U))
    ((string_reduction_pred (str.indexof x y n) U) (string_reduction_indexof x y n U))
    ; str.update
    ; str.from_int
    ; str.to_int
    ; seq.nth
    ; str.replaceall
    ; str.replace_re
    ; str.replace_re_all
    ; str.to_lower
    ; str.to_upper
    ; str.rev
    ; str.leq
  )
)

; Returns the reduction predicate and purification equality for term t
; of sort s.
(program string_reduction ((U Type) (t U))
  (U Type) Bool
  (
    ((string_reduction t U) (and (string_reduction_pred t U) (= t (skolem t))))
  )
)

; Compute the eager reduction predicate for (str.contains t r) where s
; is the sort of t and r.
; This is the formula:
;    (ite (str.contains t r) (= t (str.++ sk1 r sk2)) (not (= t r)))
(program string_eager_reduction_contains ((U Type) (t U) (r U))
  (U U Type) Bool
  (
    ((string_eager_reduction_contains t r U)
        (let ((k1 (skolem (skolem_first_ctn_pre U t r))))
        (let ((k2 (skolem (skolem_first_ctn_post U t r))))
        (ite
          (str.contains t r)
          (= t (str.++ k1 r k2))
          (not (= t r)))
        )))
  )
)

; Compute the eager reduction predicate for (str.code s), which is the formula:
;   (ite (= (str.len s) 1)
;     (and (<= 0 (str.code s)) (< (str.code s) A))
;     (= (str.code s) (- 1)))
(define-fun string_eager_reduction_to_code ((s String)) Bool
  (let ((t (str.to_code s)))
  (ite
    (= (str.len s) 1)
    (and (>= t 0) (< t 196608))
    (= t (alf.neg 1))))
)

; Compute the eager reduction predicate for (str.indexof x y n), which is the
; formula:
; (and
;   (or (= (str.indexof x y n) (- 1)) (>= (str.indexof x y n) n))
;   (<= (str.indexof x y n) (str.len x)))
(program string_eager_reduction_indexof ((U Type) (x U) (y U) (n Int))
  (U U Int) Bool
  (
    ((string_eager_reduction_indexof x y n)
        (let ((t (str.indexof x y n)))
        (and (or (= t (alf.neg 1)) (>= t n))
             (<= t (str.len x)))))
  )
)

; Compute the eager reduction predicate of term t
(program string_eager_reduction ((U Type) (x U) (y U) (n Int) (m Int))
  (U Type) Bool
  (
    ((string_eager_reduction (str.to_code x) U) (string_eager_reduction_to_code x))
    ((string_eager_reduction (str.contains x y) U) (string_eager_reduction_contains x y U))
    ((string_eager_reduction (str.indexof x y n) U) (string_reduction_indexof x y n))
  )
)

; A helper method for computing the conclusion of PfRule::RE_UNFOLD_POS.
; For a regular expression (re.++ R1 ... Rn), this returns a pair of terms
; where the first term is a concatentation (str.++ t1 ... tn) and the second
; is a conjunction M of literals of the form (str.in_re ti Ri), such that
;   (str.in_re x (re.++ R1 ... Rn))
; is equivalent to
;   (and (= x (str.++ t1 ... tn)) M)
; We use the optimization that Rj may be (str.to_re tj); otherwise tj is an
; application of the unfolding skolem program skolem_re_unfold_pos.
(program re_unfold_pos_concat ((t term) (r term) (ro term) (i mpz)) termPair
  (match r
    ((apply r1 r2)
      (match (re_unfold_pos_concat t r2 ro (mp_add i 1))
        ((pair p1 p2)
        (let r12 (getarg re.++ r1)
        (let r122 (try_getarg str.to_re r12)
        (ifequal r122 r12
          (let k (skolem_re_unfold_pos t ro i)
          (pair (str.++ k p1) (and (str.in_re k r12) p2)))
          (pair (str.++ r122 p1) p2)))))))
    (default (pair emptystr true))
))

; Returns a formula corresponding to a conjunction saying that each of the
; elements of str.++ application t is empty. For example for
;   (str.++ x (str.++ y ""))
; this returns:
;  (and (= x "") (and (= y "") true))
(program non_empty_concats ((t term) (u sort)) term
  (match t
    ((apply t1 t2)
      (and (not (= (getarg str.++ t1) (mk_emptystr u))) (non_empty_concats t2 u)))
    (default (ifequal t (mk_emptystr u) true (fail term)))))

; Get first character or empty string from term t.
; If t is of the form (str.++ (char n) ...), return (char n).
; If t is of the form emptystr, return emptystr.
; Otherwise, this side condition fails
(program string_first_char_or_empty ((t term) (u sort)) term
  (match t
    ((apply t1 t2)
      (let t12 (getarg str.++ t1)
      (match t12
        ((char n) t12)
        ((apply t121 t122) (ifequal t121 seq.unit t12 (fail term))))))
    (default (ifequal t (mk_emptystr u) t (fail term)))))

; Flatten constants in str.++ application s. Notice that the rewritten form
; of strings in cvc5 are such that constants are grouped into constants of
; length >=1 which we call "word" constants. For example, the cvc5 rewritten
; form of (str.++ "A" "B" x) is (str.++ "AB" x) which in LFSC is represented as:
;    (str.++ (str.++ (char 65) (str.++ (char 66) emptystr)) (str.++ x emptystr))
; For convenience, in this documentation, we will write this simply as:
;    (str.++ (str.++ "A" (str.++ "B" "")) (str.++ x ""))
; e.g. we assume that word constants are represented using char and emptystr.
; Many string rules rely on processing the prefix of strings, which in LFSC
; involves reasoning about the characters one-by-one. Since the above term
; has a level of nesting when word constants of size > 1 are involved, this
; method is used to "flatten" str.++ applications so that we have a uniform
; way of reasoning about them in proof rules. In this method, we take a
; str.++ application corresponding to a string term in cvc5 rewritten form.
; It returns the flattened form such that there are no nested applications of
; str.++. For example, given input:
;    (str.++ (str.++ "A" (str.++ "B" "")) (str.++ x ""))
; we return:
;    (str.++ "A" (str.++ "B" (str.++ x "")))
; Notice that this is done for all word constants in the chain recursively.
; It does not insist that the nested concatenations are over characters only.
; This rule may fail if s is not a str.++ application corresponding to a term
; in cvc5 rewritten form.
(program string_flatten ((s term) (u sort)) term
  (match s
    ((apply s1 s2)
      (let s12 (getarg str.++ s1)
        ; Must handle nested concatenation for word constant. We know there is no nested concatenation within s12, so we don't need to flatten it.
        ; Since s12 may not be a concat term, we must use n-ary intro to ensure it is in n-ary form
        (string_concat (string_nary.intro s12 u) (string_flatten s2 u) u)))
    (default (ifequal s (mk_emptystr u) s (fail term))))
)

; Helper for collecting adjacent constants. This side condition takes as input
; a str.++ application s. It returns a pair whose concatenation is equal to s,
; whose first component corresponds to a word constant, and whose second
; component is a str.++ application whose first element is not a character.
; For example, for:
;   (str.++ "A" (str.++ "B" (str.++ x "")))
; We return:
;   (pair (str.++ "A" (str.++ "B" "")) (str.++ x ""))
(program string_collect_acc ((s term) (u sort)) termPair
  (match s
    ((apply s1 s2)
      (match (getarg str.++ s1)
        ((char n)
          (match (string_collect_acc s2 u)
            ((pair ssc1 ssc2) (pair (apply s1 ssc1) ssc2))))
        (default (pair (mk_emptystr u) s))))
    (default (ifequal s (mk_emptystr u) (pair s s) (fail termPair))))
)

; Collect adjacent constants for the prefix of string s. For example:
;    (str.++ "A" (str.++ "B" (str.++ x "")))
; we return:
;    (str.++ (str.++ "A" (str.++ "B" "")) (str.++ x ""))
; This side condition may fail if s is not a str.++ application.
; Notice that the collection of constants is done for all word constants in the
; term s recursively.
(program string_collect ((s term) (u sort)) term
  (match (string_collect_acc s u)
    ((pair sc1 sc2)
      (ifequal sc1 (mk_emptystr u)
        ; did not strip a constant prefix
        (match s
          ((apply s1 s2) (apply s1 (string_collect s2 u)))
          (default (ifequal s (mk_emptystr u) s (fail term))))
        ; stripped a constant prefix, must eliminate singleton
        (str.++ (string_nary.elim sc1 u) (string_collect sc2 u)))))
)

; Strip equal prefix of s and t. This returns the pair corresponding to s and
; t after dropping the maximal equal prefix removed. For example, for:
;   (str.++ x (str.++ y (str.++ z "")))
;   (str.++ x (str.++ w ""))
; This method will return:
;   (pair (str.++ y (str.++ z "")) (str.++ w ""))
; This side condition may fail if s or t is not a str.++ application.
(program strip_prefix ((s term) (t term) (u sort)) termPair
  (match s
    ((apply s1 s2)
      (let s12 (getarg str.++ s1)
        (match t
          ((apply t1 t2)
            (let t12 (getarg str.++ t1)
              (ifequal s12 t12
                (strip_prefix s2 t2 u)
                (pair s t))))
          (default (ifequal t (mk_emptystr u) (pair s t) (fail termPair))))))
    (default (ifequal s (mk_emptystr u) (pair s t) (fail termPair))))
)

; Converts a str.++ application into "flat form" so that we are ready to
; process its prefix. This consists of the following steps:
; (1) convert s to n-ary form if it is not already a str.++ application,
; (2) flatten so that its constant prefix,
; (3) (optionally) reverse.
(program string_to_flat_form ((s term) (rev flag) (u sort)) term
  ; intro, flatten, reverse
  (string_rev (string_flatten (string_nary.intro s u) u) rev u))

; Converts a term in "flat form" to a term that is in a form that corresponds
; to one in cvc5 rewritten form. This is the dual method to
; string_to_flat_form. This consists of the following steps:
; (1) (optionally) reverse,
; (2) collect constants
; (3) eliminate n-ary form to its element if the term is a singleton list.
(program string_from_flat_form ((s term) (rev flag) (u sort)) term
  ; reverse, collect, elim
  (string_nary.elim (string_collect (string_rev s rev u) u) u))
