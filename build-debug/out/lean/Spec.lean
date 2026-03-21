import Cpc.SmtModel
import Cpc.Logos

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


/- Definitions for theorems -/

/- Definition of refutation -/

inductive eo_is_refutation : Term -> CCmdList -> Prop
  | intro (F : Term) (c : CCmdList) : 
    (__eo_checker_is_refutation F c) = true -> (eo_is_refutation F c)


/-
A definition of terms in the object language.
This is to be defined externally.
-/
abbrev ObjectTerm := SmtTerm

/-
A predicate defining a relation on terms in the object language and Booleans
such that (s,b) is true if s evaluates to b.
This is to be defined externally.
-/
abbrev obj_interprets := smt_interprets

abbrev ObjectModel := SmtModel

/-
Definitions for eo_is_obj
-/
mutual

def __eo_to_smt_datatype_cons : DatatypeCons -> SmtDatatypeCons
  | DatatypeCons.unit => SmtDatatypeCons.unit
  | (DatatypeCons.cons U c) => (SmtDatatypeCons.cons (__eo_to_smt_type U) (__eo_to_smt_datatype_cons c))


def __eo_to_smt_datatype : Datatype -> SmtDatatype
  | (Datatype.sum c d) => (SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d))
  | Datatype.null => SmtDatatype.null


def __eo_to_smt_type : Term -> SmtType
  | Term.Bool => SmtType.Bool
  | (Term.DatatypeType s d) => (SmtType.Datatype s (__eo_to_smt_datatype d))
  | (Term.USort i) => (SmtType.USort i)
  | Term.Int => SmtType.Int
  | Term.Real => SmtType.Real
  | (Term.Apply Term.BitVec (Term.Numeral n1)) => (SmtType.BitVec n1)
  | Term.Char => SmtType.Char
  | (Term.Apply Term.Seq x1) => (SmtType.Seq (__eo_to_smt_type x1))
  | T => SmtType.None


def __eo_to_smt : Term -> SmtTerm
  | (Term.Boolean b) => (SmtTerm.Boolean b)
  | (Term.Numeral n) => (SmtTerm.Numeral n)
  | (Term.Rational r) => (SmtTerm.Rational r)
  | (Term.String s) => (SmtTerm.String s)
  | (Term.Binary w n) => (SmtTerm.Binary w n)
  | (Term.Var s T) => (SmtTerm.Var s (__eo_to_smt_type T))
  | (Term.DtCons s d i) => (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)
  | (Term.DtSel s d i j) => (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j)
  | (Term.UConst i T) => (SmtTerm.UConst (smt_lit_uconst_id i) (__eo_to_smt_type T))
  | (Term.Apply Term.not x1) => (SmtTerm.Apply SmtTerm.not (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.and x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.eq x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply f y) => (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y))
  | y => SmtTerm.None




end 

/-
An inductive predicate defining the correspondence between Eunoia terms
and terms in the object language.
(t,s) is true if the Eunoia term represents a term s in the object language.
This is to be custom defined in the Eunoia-to-Lean compiler based on the
target definition of ObjectTerm.
-/
inductive eo_is_obj : Term -> ObjectTerm -> Prop
  | intro (x : Term) : eo_is_obj x (__eo_to_smt x)



/-
A predicate defining when a Eunoia term corresponds to an object term that
evaluates to true or false.
(t,b) is true if t is a Eunoia term corresponding to an object term that
evaluates to b.
-/
def eo_interprets (M : ObjectModel) (t : Term) (b : Bool) : Prop :=
  exists (s : ObjectTerm), (eo_is_obj t s) /\ (obj_interprets M s b)

/- ---------------------------------------------- -/

