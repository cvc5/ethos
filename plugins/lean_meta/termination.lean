-- Termination clauses for the generated Lean definitions.
--
-- Lean has to be told why a recursive definition terminates whenever it cannot
-- see this for itself, and no measure the compiler could guess would do for the
-- programs below. So the clause is stated here as the Lean text it is, and the
-- lean-meta plugin appends it verbatim to the definition of the program named,
-- see LeanMetaReduce::readTerminationClauses.
--
-- A block runs from a line naming one or more programs, written `-- $name ...`,
-- to the next comment line. Naming several programs in one block gives them
-- all the same clause; prose may be written between blocks, since a clause is
-- Lean text and holds no comment of its own.
--
-- A clause may not name the native layer. It is appended to a generated
-- definition rather than written into a resource, so it is not one of the
-- blocks that layer is trimmed by and a name it gave would keep nothing
-- alive. Every native type abbreviates a Lean type, which is what a measure
-- writes instead. See LeanMetaReduce::trimNativeDefs.
--
-- This file is for the programs of the deep embedding, which every input is
-- compiled through. A program of the *input* signature is named in a file of
-- its own, which the compiler is given with --lean-config, e.g.
-- plugins/lean_meta/cpc_termination.lean for CPC.

-- Datatype defaults recurse through a mutually inductive type/declaration
-- tree. The declaration suffix is the datatype recursion budget; the small
-- offsets orient calls through datatype, constructor, and field helpers.

-- $smtx_type_default
termination_by T => 2 * sizeOf T

-- $smtx_datatype_decl_default
termination_by ddF => 2 * sizeOf ddF

-- $smtx_datatype_default
termination_by dF ddF => 2 * (sizeOf dF + sizeOf ddF) + 1

-- $smtx_datatype_cons_default
termination_by c ddF => 2 * (sizeOf c + sizeOf ddF) + 2

-- $smtx_field_type_default
termination_by T ddF => 2 * (sizeOf T + sizeOf ddF) + 3
decreasing_by
  all_goals simp_wf
  all_goals omega

-- Type boundedness (unit/finite) computes a fixpoint over datatype
-- declarations. The lexicographic measures decrease on the structural
-- component for descents into subterms, on the pass countdown for the
-- fixpoint iteration, and on the final component for the tie between
-- field types and their recheck as ordinary types.

-- $smtx_type_bounded
termination_by T => (sizeOf T, 0)

-- $smtx_datatype_decl_bounded
termination_by ddC dd ddB => (sizeOf dd, sizeOf ddC)

-- $smtx_datatype_decl_bounded_step
termination_by ddR ddB => (sizeOf ddR, 0)

-- $smtx_datatype_bounded
termination_by dF ddB => (sizeOf dF, 0)

-- $smtx_datatype_cons_bounded
termination_by c ddB => (sizeOf c, 0)

-- $smtx_field_type_bounded
termination_by T ddB => (sizeOf T, 1)

-- The evaluator recurses structurally, and the theorem that follows it caches
-- the equation for a Boolean term, which Lean would otherwise unfold anew at
-- every use.

-- $smtx_model_eval
termination_by structural t => t

private theorem __smtx_model_eval_eqns_cache (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  unfold __smtx_model_eval
  rfl
