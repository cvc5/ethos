/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_H
#define PLUGIN_H

#include <string>

#include "attr.h"
#include "expr.h"
#include "expr_info.h"
#include "util/filesystem.h"

namespace alfc {

/**
 * A plugin class. This is a virtual base class that receives callbacks from
 * the core of the ALFC checker.
 *
 * An example use of this class is to compile an ALF signature to C++.
 */
class Plugin
{
public:
  Plugin() {}
  virtual ~Plugin() {}
  /**
   * Reset. Called when the command reset is called.
   */
  virtual void reset() {}
  /**
   * Push scope. Called when assume-push is called, or when the expression
   * parser pushes an internal scope.
   */
  virtual void pushScope() {}
  /**
   * Pop scope. Called when step-pop is called, or when the expression
   * parser pops an internal scope.
   */
  virtual void popScope() {}
  /**
   * Include file, if not already done so.
   * @param s Specifies the path and name of the file to include.
   */
  virtual void includeFile(const Filepath& s) {}
  /**
   * Set type rule for literal kind k to t. This is called when the
   * command declare-consts is executed.
   * @param k The kind to associate, e.g. NUMERAL.
   * @param t The type to associate terms of that kind with, e.g. the
   * integer tpye.
   */
  virtual void setLiteralTypeRule(Kind k, const Expr& t) {}
  /**
   * Called when expression e is bound to the given name.
   * @param name The name we are binding.
   * @param e The expression that name is bound to.
   */
  virtual void bind(const std::string& name, const Expr& e) {}
  /**
   * Mark constructor kind.
   * @param v The term to mark constructor kind, e.g. or
   * @param a The constructor kind of v, e.g. Attr::RIGHT_ASSOC_NIL.
   * @param cons The associated constructor term. For example, if a is
   * Attr::RIGHT_ASSOC_NIL, then cons is the nil terminator for v.
   */
  virtual void markConstructorKind(const Expr& v, Attr a, const Expr& cons) {}
  /**
   * Mark oracle command. Called when declare-oracle-fun is executed.
   * @param v The variable corresponding to the oracle function.
   * @param ocmd The command specified as the command to run the oracle.
   */
  virtual void markOracleCmd(const Expr& v, const std::string& ocmd) {}
  /**
   * Define program. Called when a program is declared via program.
   * @param v The variable corresponding to the program.
   * @param prog Its definition, which is a term of kind PROGRAM.
   */
  virtual void defineProgram(const Expr& v, const Expr& prog) {}
  //--------- evaluation
  /**
   * Finalize. Called once when the proof checker has finished parsing all input.
   */
  virtual void finalize() {}
};

}  // namespace alfc

#endif /* STATE_H */
