/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "executor.h"

namespace alfc {
  
std::string Executor::showCompiledFiles()
{
  return "";
}

void Executor::initialize()
{
}

Expr Executor::getType(ExprValue* hdType,
                       const std::vector<ExprValue*>& args,
                       std::ostream* out)
{
  return d_null;
}

Expr Executor::evaluate(ExprValue* e, Ctx& ctx) { return d_null; }

ExprValue* Executor::evaluateProgramInternal(const std::vector<ExprValue*>& args,
                                            Ctx& ctx)
{
  return nullptr;
}

}
