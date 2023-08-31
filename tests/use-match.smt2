
(declare-type Pair (Type Type))
(declare-const pair (-> (! Type :var U :implicit) (! Type :var T :implicit) U T (Pair U T)))
(declare-const = (-> (! Type :var T :implicit) T T Bool))

; nary.append cons c xs
; Appends `c` to the head of `xs`.
(program nary.append
    ((L Type) (cons (-> L L L)) (c L) (xs L :list))
    ((-> L L L) L L) L
    (
        ((nary.append cons c xs) (cons c xs))
    )
)

; concat cons xs ys
; Concatenates two lists `xs` and `ys`.
(program nary.concat
    ((L Type) (cons (-> L L L)) (x L) (xs L :list) (ys L))
    ((-> L L L) L L) L
    (
        ((nary.concat cons alf.nil ys) ys)
        ((nary.concat cons (cons x xs) ys) (nary.append cons x (nary.concat cons xs ys)))
    )
)

(declare-sort String 0)
(declare-consts <string> String)
(declare-const str.++ (-> String String String) :right-assoc-nil)

; `check_true b`
; returns true if b is true, returns false otherwise
(program check_true ((b Bool))
  (Bool) Bool
  (
    ((check_true true) true)
    ((check_true b) false)
  )
)
(define check_length_one ((s String)) (check_true (alf.is_eq (alf.len s) 1)))

(program string_collect_acc ((t String) (tail String :list))
  (String) (Pair String String)
  (
    ((string_collect_acc alf.nil)         (pair alf.nil alf.nil))
    ; Check if t is a word constant
    ((string_collect_acc (str.++ t tail))
      (alf.ite (check_length_one t)
        (alf.match ((s1 String) (s2 String)) 
          (string_collect_acc tail)
          ((pair alf.nil s2) (pair t s2))
          ((pair s1 s2) (pair (alf.concat t s1) s2))
        )
        (pair alf.nil (str.++ t tail))))
  )
)


(declare-rule collect_acc ((s String))
  :args (s)
  :conclusion (alf.match ((s1 String) (s2 String :list)) 
                (string_collect_acc s) 
                ((pair alf.nil s2)  (= s s2))
                ((pair s1 s2)       (= s (str.++ s1 s2)))
              )
)

(declare-fun x () String)
(step @p0 (= (str.++ "A" "B" x) (str.++ "AB" x)) :rule collect_acc :args ((str.++ "A" "B" x)))
