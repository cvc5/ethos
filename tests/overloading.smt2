(declare-sort Int 0)
(declare-sort Real 0)

(program arithTypeRule ()
    (Type Type) Type
    (
      ((arithTypeRule Int Int) Int)
      ((arithTypeRule Int Real) Real)
      ((arithTypeRule Real Int) Real)
      ((arithTypeRule Real Real) Real)
    )
)

(declare-const + (-> (! Type :var T :implicit) 
                     (! Type :var U :implicit) 
                     T U (arithTypeRule T U)))


(declare-const = (-> (! Type :var T :implicit) T T Bool))


(declare-consts <numeral> Int)
(declare-consts <decimal> Real)


(assume a1 (= (+ 1.0 1) (+ 2.0 2)))
