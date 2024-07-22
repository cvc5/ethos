/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "executor.h"
#include "state.h"

namespace ethos {
  
Executor::Executor(State& s) : d_state(s), d_tc(s.getTypeChecker()) {}

Executor::~Executor() {}
  
bool Executor::hasEvaluation(ExprValue* e)
{
  return e->isCompiled();
}

Expr Executor::evaluateProgram(ExprValue* prog,
                               const std::vector<ExprValue*>& args,
                               Ctx& ctx)
{
  ExprValue * ev = evaluateProgramInternal(args, ctx);
  if (ev==nullptr)
  {
    return d_null;
  }
  return Expr(ev);
}

}
