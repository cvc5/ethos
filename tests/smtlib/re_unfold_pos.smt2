(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)

(assert (str.in_re x (re.++ (re.* re.allchar) (str.to_re "A") (re.* re.allchar) (str.to_re "D") (re.* re.allchar))))
(assert (< (str.len y) 2))

(assert (or (= x (str.++ y "BCA")) (= x "DDD")))
(check-sat)
