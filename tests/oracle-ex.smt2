(declare-sort Int 0)
(declare-consts <numeral> Int)
(declare-sort String 0)
(declare-consts <string> String)
(declare-const or (-> Bool Bool Bool) :right-assoc-nil)
(declare-const and (-> Bool Bool Bool) :right-assoc-nil)
(declare-const not (-> Bool Bool))
(declare-sort @AtomMapping 0)
(declare-const @am.nil @AtomMapping)
(declare-const @am.cons (-> Int Bool @AtomMapping @AtomMapping))

; ./dratt-verify.sh takes:
; - An mapping (@AtomMapping) that maps atoms to unique identifiers.
; - A conjunction of input clauses.
; - A DRAT proof file, whose file name is given as a String.
; It returns "true" if the preamble of the DRAT proof file matches
; the input clauses, as determined by the first two arguments.

(declare-oracle-fun dratt-verify (@AtomMapping Bool String) Bool ./dratt-verify.sh)

; ./drat-check.sh
; - A DRAT proof file, whose file name is given as a String.
; It returns "true" if the DRAT proof file is a valid refutation proof.

(declare-oracle-fun drat-check (String) Bool ./drat-check.sh)

; The DRAT proof rule.
; Takes arbitrary list of premises, an atom mapping, and the file name of a DRAT
; proof and invokes the two oracles above.

(declare-rule drat ((F Bool) (P String) (m @AtomMapping))
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

;(step @p5 false :rule drat :premises (@p1 @p2 @p3 @p4) :args ((@am.cons 1 A (@am.cons 2 B (@am.cons 3 C @am.nil))) "drat-proof.txt"))
