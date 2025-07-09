/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "flatten_eval.h"

namespace ethos {

FlattenEval::FlattenEval(State& s) : StdPlugin(s) {}
FlattenEval::~FlattenEval(){}

std::vector<ProgramOut> FlattenEval::flattenEval(const Expr& v, const Expr& caseBody, std::ostream& os)
{
  std::vector<ProgramOut> ret;
  size_t pcount = 0;
  size_t vcount = 0;

  return ret;
}

}  // namespace ethos

