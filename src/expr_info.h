/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef EXPR_INFO_H
#define EXPR_INFO_H

#include <map>
#include <string>
#include <memory>

#include "kind.h"
#include "attr.h"
#include "expr.h"

namespace ethos {

using AttrMap = std::map<Attr, std::vector<Expr>>;

/**
 * Information about how to construct applications of a function.
 */
class AppInfo
{
public:
  AppInfo() : d_attrCons( ), d_kind(Kind::NONE), d_isOverloaded(false) {}
  /** Attribute */
  Attr d_attrCons;
  /** Attribute */
  Expr d_attrConsTerm;
  /** Associated kind */
  Kind d_kind;
  /**
   * Whether this symbol is overloaded. The overloads for this symbol are
   * maintained in State::d_overloads[d_overloadName].
   */
  bool d_isOverloaded;
  /**
   * The name of the symbol, if overloaded. Note this is required to be
   * stored explicitly to handle cases where symbols are bound to terms that do
   * not have their given name, e.g. (define s () (+ 1 1)) maps "s" to the term
   * (+ 1 1), which does not have the name "s".
   */
  std::string d_overloadName;
};

}  // namespace ethos

#endif /* STATE_H */
