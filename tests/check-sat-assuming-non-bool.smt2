; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Int)
(check-sat-assuming (x))
