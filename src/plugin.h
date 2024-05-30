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
  virtual void reset() = 0;
  /**
   * Push scope. Called when assume-push is called.
   */
  virtual void pushScope() = 0;
  /**
   * Pop scope. Called when step-pop is called.
   */
  virtual void popScope() = 0;
  /**
   * Include file, if not already done so.
   * @param s Specifies the path and name of the file to include.
   */
  virtual void includeFile(const Filepath& s) = 0;
  /**
   * Set type rule for literal kind k to t. This is called when the
   * command declare-consts is executed.
   * @param k The kind to associate, e.g. NUMERAL.
   * @param t The type to associate terms of that kind with, e.g. the
   * integer tpye.
   */
  virtual void setLiteralTypeRule(Kind k, const Expr& t) = 0;
  /**
   * Called when expression e is bound to the given name.
   * @param name The name we are binding.
   * @param e The expression that name is bound to.
   */
  virtual void bind(const std::string& name, const Expr& e) = 0;
  /**
   * Mark constructor kind.
   * @param v The term to mark constructor kind, e.g. or
   * @param a The constructor kind of v, e.g. Attr::RIGHT_ASSOC_NIL.
   * @param cons The associated constructor term. For example, if a is
   * Attr::RIGHT_ASSOC_NIL, then cons is the nil terminator for v.
   */
  virtual void markConstructorKind(const Expr& v, Attr a, const Expr& cons) = 0;
  /**
   * Mark oracle command. Called when declare-oracle-fun is executed.
   * @param v The variable corresponding to the oracle function.
   * @param ocmd The command specified as the command to run the oracle.
   */
  virtual void markOracleCmd(const Expr& v, const std::string& ocmd) = 0;
  /**
   * Define program. Called when a program is declared via program.
   * @param v The variable corresponding to the program.
   * @param prog Its definition, which is a term of kind PROGRAM.
   */
  virtual void defineProgram(const Expr& v, const Expr& prog) = 0;
  /**
   * Finalize. Called once when the proof checker has finished parsing all input.
   */
  virtual void finalize() = 0;
};

}  // namespace alfc

#endif /* STATE_H */
