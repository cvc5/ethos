/******************************************************************************
 * This file is part of the ethos project.
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

namespace ethos {

/**
 * A plugin class. This is a virtual base class that receives callbacks from
 * the core of the EO checker.
 *
 * An example use of this class is to compile an Eunoia signature to C++.
 */
class Plugin
{
public:
  Plugin() {}
  virtual ~Plugin() {}
  //--------- initialize
  /**
   * Initialize. Called when the proof checker is initalized with this plugin.
   */
  virtual void initialize() {}
  //--------- parsing
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
   * @param isReference Whether the given file was marked as a reference file.
   * @param referenceNf The method for normalizing the reference file, if one exists.
   */
  virtual void includeFile(const Filepath& s, bool isReference, const Expr& referenceNf) {}
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
   * Define program. Called when a program is declared via program.
   * @param v The variable corresponding to the program.
   * @param prog Its definition, which is a term of kind PROGRAM.
   */
  virtual void defineProgram(const Expr& v, const Expr& prog) {}
  //--------- evaluation
  /**
   * @return true if this plugin implements the evaluation methods below for
   * type, expression or program e.
   */
  virtual bool hasEvaluation(ExprValue* e) { return false; }
  /**
   * Evaluate.
   * @param e The expression to evaluate
   * @param ctx The context under which we are evaluating, which is a
   * substitution from variables to their value.
   * @return The result of evaluation e in context ctx.
   */
  virtual Expr evaluate(ExprValue* e, Ctx& ctx) { return Expr(); }
  /**
   * Evaluate program.
   * @param prog The program to evaluate.
   * @param args The arguments of the program application. Note that prog is
   * included in this list, at position 0 of args.
   * @param ctx The context under which we are evaluating, which is a
   * substitution from variables to their value.
   * @return The result of evaluation prog for the given argumetns in context
   * ctx.
   */
  virtual Expr evaluateProgram(ExprValue* prog,
                               const std::vector<ExprValue*>& args,
                               Ctx& newCtx) { return Expr(); }
  //--------- finalize
  /**
   * Finalize. Called once when the proof checker has finished parsing all input.
   */
  virtual void finalize() {}
};

}  // namespace ethos

#endif /* STATE_H */
