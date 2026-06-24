/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#ifndef PLUGIN_SMT_META_UTILS_H
#define PLUGIN_SMT_META_UTILS_H

#include <map>
#include <sstream>

#include "../utils.h"
#include "state.h"

namespace ethos {

/** A utility for printing conjunctions */
class ConjPrint
{
 public:
  ConjPrint();
  void push(const std::string& str);
  void printConjunction(std::ostream& os, bool isDisj = false);
  bool empty() const { return d_npush == 0; }
  std::stringstream d_ss;
  size_t d_npush;
};

class SelectorCtx
{
 public:
  SelectorCtx();
  void clear();
  /**
   * Maps parameters to a string representation of what
   * that parameter was mapped to. This is a chain of
   * datatype selectors, where we do not model the AST
   * of this chain.
   */
  std::map<Expr, std::string> d_ctx;
  /** The context it was matched in */
  std::map<Expr, MetaKind> d_tctx;
};

}  // namespace ethos

#endif
