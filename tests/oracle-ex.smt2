(declare-sort Int 0)
(declare-consts <numeral> Int)
(declare-sort String 0)
(declare-consts <string> String)
(declare-const or (-> Bool Bool Bool) :right-assoc-nil)
(declare-const and (-> Bool Bool Bool) :right-assoc-nil)
(declare-const not (-> Bool Bool))
(declare-sort @LitMapping 0)
(declare-const @lm.nil @LitMapping)
(declare-const @lm.cons (-> Int Bool @LitMapping @LitMapping))

(declare-oracle-fun dratt-verify (@LitMapping Bool String) Bool ./dratt-verify.sh)
(declare-oracle-fun drat-check (String) Bool ./drat-check.sh)

(declare-rule drat ((F Bool) (P String) (m @LitMapping))
  :premise-list F and
  :args (m P)
  :requires (((dratt-verify m F P) true) ((drat-check P) true))
  :conclusion false
)

(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)

(assume @p1 (or A B C))
(assume @p2 (not A))
(assume @p3 (not B))
(assume @p4 (or B (not C)))

;(step @p5 false :rule drat :premises (@p1 @p2 @p3 @p4) :args ((@lm.cons 1 A (@lm.cons 2 B (@lm.cons 3 C @lm.nil))) "drat-proof.txt"))
