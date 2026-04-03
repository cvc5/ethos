/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef EXPR_BUILDER_H
#define EXPR_BUILDER_H

#include <vector>

#include "expr.h"
#include "expr_info.h"

namespace ethos {

class State;

namespace expr_builder {

Expr mkExpr(State& state, Kind k, const std::vector<Expr>& children);
Expr mkApply(State& state, const std::vector<Expr>& children);
Expr mkApplyAttr(State& state,
                 AppInfo* ai,
                 const std::vector<ExprValue*>& vchildren,
                 const Expr& consTerm);

}  // namespace expr_builder

}  // namespace ethos

#endif
