module

public import $EO_CALC$.Logos
import all $EO_CALC$.Logos
public import $EO_CALC$.SmtTranslate
import all $EO_CALC$.SmtTranslate
public import $EO_CALC$.SmtModel
import all $EO_CALC$.SmtModel

/-!
The cases of the programs, one function each, as a backend that tries a
program's cases in order computes them: `some` of the case's result where
its pattern matches, `none` where it does not. A parameter that the
program's pattern repeats is a test for equality here, and a failed test is
"no match". The programs themselves (Logos.lean and the modules beside it)
say the same with linear patterns, requirements and continuation programs.

Nothing in the checker uses these definitions. They are for relating
another backend's code, case by case, to the programs.
-/

@[expose] public section

open SmtEval
open Eo
open Smtm

set_option linter.unusedVariables false
set_option linter.internalConstructors false
set_option maxHeartbeats 10000000

noncomputable section

namespace EoCases

$LEAN_CASE_DEFS$
end EoCases
