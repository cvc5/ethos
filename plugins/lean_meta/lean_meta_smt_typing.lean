module

public import $EO_CALC$.SmtSyntax
import all $EO_CALC$.SmtSyntax

@[expose] public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

-- The static interface of SMT-LIB: typing and well-formedness. Nothing here
-- names a value or a model, so the checker, which computes these, is built
-- without the model semantics.
-- $ What of the semantics comes out here rather than in SmtModel is read off
-- $ what each program names, see LeanMetaReduce::finalizeSmtPrograms.

-- The primitive operations the static interface uses and no module above it.
-- $ See LeanMetaReduce::nativeDefs.
$NATIVE_DEFS$

/- Definition of the static interface of SMT-LIB -/

mutual

/-- Whether `__smtx_type_default` constructs a value for `T`. Base types are
inhabited, a map type is inhabited when its range is, and a datatype is
inhabited when one of its constructors has inhabited fields. As in the default
generator, a field `TypeRef s` is resolved among the declarations that follow
the current one, which is what makes the recursion well founded. -/
def native_inhabited_type : SmtType -> native_Bool
  | SmtType.None => false
  | SmtType.TypeRef _ => false
  | SmtType.DtcAppType _ _ => false
  | SmtType.Map _ U => native_inhabited_type U
  | SmtType.Datatype s dd => __smtx_decl_inhabited s dd
  | _ => true
termination_by T => 2 * sizeOf T

def __smtx_decl_inhabited (s : native_String) : SmtDatatypeDecl -> native_Bool
  | SmtDatatypeDecl.cons sF dF ddF =>
    native_ite (native_streq s sF) (__smtx_dt_inhabited dF ddF) (__smtx_decl_inhabited s ddF)
  | SmtDatatypeDecl.nil => false
termination_by ddF => 2 * sizeOf ddF

def __smtx_dt_inhabited : SmtDatatype -> SmtDatatypeDecl -> native_Bool
  | SmtDatatype.sum c d, ddF =>
    native_or (__smtx_dt_cons_inhabited c ddF) (__smtx_dt_inhabited d ddF)
  | SmtDatatype.null, _ => false
termination_by d ddF => 2 * (sizeOf d + sizeOf ddF) + 1

def __smtx_dt_cons_inhabited : SmtDatatypeCons -> SmtDatatypeDecl -> native_Bool
  | SmtDatatypeCons.cons (SmtType.TypeRef s) c, ddF =>
    native_and (__smtx_decl_inhabited s ddF) (__smtx_dt_cons_inhabited c ddF)
  | SmtDatatypeCons.cons T c, ddF =>
    native_and (native_inhabited_type T) (__smtx_dt_cons_inhabited c ddF)
  | SmtDatatypeCons.unit, _ => true
termination_by c ddF => 2 * (sizeOf c + sizeOf ddF) + 2

end

$LEAN_SMT_TYPING_DEFS$

end Smtm
