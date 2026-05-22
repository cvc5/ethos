import Cpc.SmtModel
import Cpc.Logos

open SmtEval
open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-
Definitions for eo_to_smt_type, eo_to_smt
-/
noncomputable section

def native_reserved_datatype_name (s : native_String) : native_Bool :=
  s.startsWith "@"

mutual

def __eo_to_smt_datatype_cons : DatatypeCons -> SmtDatatypeCons
  | DatatypeCons.unit => SmtDatatypeCons.unit
  | (DatatypeCons.cons U c) => (SmtDatatypeCons.cons (__eo_to_smt_type U) (__eo_to_smt_datatype_cons c))


def __eo_to_smt_datatype : Datatype -> SmtDatatype
  | (Datatype.sum c d) => (SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d))
  | Datatype.null => SmtDatatype.null


def __eo_to_smt_type : Term -> SmtType
  | Term.Bool => SmtType.Bool
  | (Term.DatatypeType s d) => (native_ite (native_reserved_datatype_name s) SmtType.None (SmtType.Datatype s (__eo_to_smt_datatype d)))
  | (Term.DatatypeTypeRef s) => (native_ite (native_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s))
  | (Term.DtcAppType T1 T2) => 
    let _v0 := (__eo_to_smt_type T2)
    let _v1 := (__eo_to_smt_type T1)
    (__smtx_typeof_guard _v1 (__smtx_typeof_guard _v0 (SmtType.DtcAppType _v1 _v0)))
  | (Term.USort i) => (SmtType.USort i)
  | (Term.Apply (Term.Apply Term.FunType T1) T2) => 
    let _v0 := (__eo_to_smt_type T2)
    let _v1 := (__eo_to_smt_type T1)
    (__smtx_typeof_guard _v1 (__smtx_typeof_guard _v0 (SmtType.FunType _v1 _v0)))
  | (Term.UOp UserOp.Int) => SmtType.Int
  | (Term.UOp UserOp.Real) => SmtType.Real
  | (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n1)) => (native_ite (native_zleq 0 n1) (SmtType.BitVec (native_int_to_nat n1)) SmtType.None)
  | (Term.UOp UserOp.Char) => SmtType.Char
  | (Term.Apply (Term.UOp UserOp.Seq) x1) => 
    let _v0 := (__eo_to_smt_type x1)
    (__smtx_typeof_guard _v0 (SmtType.Seq _v0))
  | T => SmtType.None


def __eo_to_smt : Term -> SmtTerm
  | (Term.Boolean b) => (SmtTerm.Boolean b)
  | (Term.Numeral n) => (SmtTerm.Numeral n)
  | (Term.Rational r) => (SmtTerm.Rational r)
  | (Term.String s) => (SmtTerm.String s)
  | (Term.Binary w n) => (SmtTerm.Binary w n)
  | (Term.Var (Term.String s) T) => (SmtTerm.Var s (__eo_to_smt_type T))
  | (Term.DtCons s d i) => (native_ite (native_reserved_datatype_name s) SmtTerm.None (SmtTerm.DtCons s (__eo_to_smt_datatype d) i))
  | (Term.DtSel s d i j) => (native_ite (native_reserved_datatype_name s) SmtTerm.None (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j))
  | (Term.UConst i T) => (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
  | (Term.Apply (Term.UOp UserOp.not) x1) => (SmtTerm.not (__eo_to_smt x1))
  | (Term.Apply (Term.Apply (Term.UOp UserOp.or) x1) x2) => (SmtTerm.or (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.UOp UserOp.and) x1) x2) => (SmtTerm.and (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x1) x2) => (SmtTerm.imp (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) x2) => (SmtTerm.eq (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply f y) => (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y))
  | y => SmtTerm.None




end

end

/-
Eunoia satisfiability depends on SMT satisfiability.
-/
def eo_satisfiability (t : Term) (b : Bool) : Prop :=
  (smt_satisfiability (eo_to_smt t) b)


/- ---------------------------------------------- -/
