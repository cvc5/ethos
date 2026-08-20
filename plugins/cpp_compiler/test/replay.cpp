/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include <cstdlib>

#include "executor.h"
#include "literal.h"
#include "state.h"

using namespace ethos;

namespace {

Expr findKind(const Expr& expr, Kind kind)
{
  if (expr.getKind() == kind)
  {
    return expr;
  }
  for (size_t i = 0, size = expr.getNumChildren(); i < size; ++i)
  {
    Expr result = findKind(expr[i], kind);
    if (!result.isNull())
    {
      return result;
    }
  }
  return Expr();
}

}  // namespace

int main()
{
  Options options;
  Stats stats;
  State state(options, stats);
  Executor executor(state);
  state.setPlugin(&executor);

  Expr intType = state.getVar("Int");
  Expr sum = state.getVar("sum");
  Expr first = state.getVar("first");
  Expr makeVar = state.getVar("make-var");
  Expr hexZero = state.getVar("hex-zero");
  Expr nil = state.getVar("nil");
  Expr trusted = state.getProofRule("trusted");
  if (intType.isNull() || sum.isNull() || first.isNull() || makeVar.isNull()
      || hexZero.isNull() || nil.isNull() || trusted.isNull())
  {
    std::exit(4);
  }
  if (state.getAttributeKind(sum.getValue()) != Attr::LEFT_ASSOC
      || !state.isProofRuleSorry(trusted.getValue()))
  {
    std::exit(5);
  }

  Expr program = state.getProgram(first.getValue());
  if (program.isNull()
      || state.getAttributeKind(program[0][0][2].getValue()) != Attr::LIST)
  {
    std::exit(6);
  }

  Expr variableProgram = state.getProgram(makeVar.getValue());
  Expr variable = findKind(variableProgram, Kind::VARIABLE);
  if (variable.isNull() || variable.getNumChildren() != 2)
  {
    std::exit(10);
  }

  Expr hexProgram = state.getProgram(hexZero.getValue());
  Expr hex = findKind(hexProgram, Kind::HEXADECIMAL);
  const Literal* hexLiteral =
      hex.isNull() ? nullptr : hex.getValue()->asLiteral();
  if (hexLiteral == nullptr || hexLiteral->d_bv.getSize() != 8)
  {
    std::exit(11);
  }

  ExprValue* nilTypeValue = state.lookupType(nil.getValue());
  Expr disambiguationProgram =
      nilTypeValue == nullptr
          ? Expr()
          : findKind(Expr(nilTypeValue), Kind::PROGRAM_CONST);
  if (disambiguationProgram.isNull()
      || state.getProgram(disambiguationProgram.getValue()).isNull())
  {
    std::exit(12);
  }

  Expr one = state.mkLiteral(Kind::NUMERAL, "1");
  Expr two = state.mkLiteral(Kind::NUMERAL, "2");
  Expr oneForType = one;
  if (state.getTypeChecker().getType(oneForType) != intType)
  {
    std::exit(7);
  }

  // The executor only auto-parses. Program evaluation must fall back to the
  // ordinary interpreter and still produce the expected result.
  Expr result = state.getTypeChecker().evaluateProgramApp({first, one, two});
  if (result != one)
  {
    std::exit(8);
  }

  // State asks the executor whether it handled the include. The generated
  // callback recognizes the source, so State does not parse and redeclare it.
  if (!state.includeFile(ETHOS_CPP_COMPILER_TEST_SIGNATURE, true)
      || Executor::showCompiledFiles().empty())
  {
    std::exit(9);
  }
  std::exit(0);
}
