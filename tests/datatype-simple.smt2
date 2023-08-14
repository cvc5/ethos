
(declare-const = (-> (! Type :var T :implicit) T T Bool))

(declare-datatypes ((nat 0)(list 0)(tree 0))
  (((succ (pred nat)) (zero))((cons (car tree) (cdr list)) (null))((node (data nat) (children list)) (leaf))))
(declare-fun x () nat)
(declare-fun y () list)
(declare-fun z () tree)
(assume a1 (= x (succ zero)))
