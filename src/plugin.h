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
   * @param isReference Whether the given file was marked as a signature file.
   * @param isReference Whether the given file was marked as a reference file.
   * @param referenceNf The method for normalizing the reference file, if one
   * exists.
   */
  virtual void includeFile(const Filepath& s,
                           bool isSignature,
                           bool isReference,
                           const Expr& referenceNf)
  {
  }
  /**
   * Same as above, but called immediately after a file has been parsed.
   */
  virtual void finalizeIncludeFile(const Filepath& s,
                                   bool isSignature,
                                   bool isReference,
                                   const Expr& referenceNf)
  {
  }
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
  /**
   * Define. Called when a define or define-fun command is executed.
   * @param name The name we are binding.
   * @param e The expression that name is bound to.
   */
  virtual void define(const std::string& name, const Expr& e) {}
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
   * @return The result of evaluation prog for the given arguments in context
   * ctx, or null if the plugin does not evaluate this application.
   */
  virtual Expr evaluateProgram(ExprValue* prog,
                               const std::vector<ExprValue*>& args,
                               Ctx& newCtx) { return Expr(); }
  /**
   * Notify assume, called when an assume command is parsed.
   * @param name The name of the assumption.
   * @param proven The formula that it assumes.
   * @param isPush true iff the assumption was from an assume-push command.
   */
  virtual void notifyAssume(const std::string& name, Expr& proven, bool isPush)
  {
  }
  /**
   * Notify step, called when a step command is parsed.
   * This method determines the argument list to a proof rule in a step or
   * step-pop and computes the result of what the step proves.
   * Note that if result is not set to a fully evaluated term,
   * then a proof checking error will occur, in which case this plugin should
   * print an error to stream err if it is provided.
   * @param name The name of the step.
   * @param rule The proof rule being applied.
   * @param proven The conclusion of the proof rule, if provided.
   * @param premises The provided premises of the proof rule.
   * @param args The provided arguments of the proof rule.
   * @param isPop Whether we were a step-pop.
   * @param result The result proven by the step.
   * @param err If provided, details on errors are printed to this stream.
   * @return true if we successfully computed result. Otherwise, this plugin
   * does not have special support for the proof step.
   */
  virtual bool notifyStep(const std::string& name,
                          Expr& rule,
                          Expr& proven,
                          const std::vector<Expr>& premises,
                          const std::vector<Expr>& args,
                          bool isPop,
                          Expr& result,
                          std::ostream* err)
  {
    return false;
  }
  /**
   * Return true if the echo should be printed. If we return false, the
   * assumption is that the message was intended for this plugin.
   * @param msg The message.
   * @return true if the caller should print the message.
   */
  virtual bool echo(const std::string& msg) { return true; }
  //--------- finalize
  /**
   * Finalize. Called once when the proof checker has finished parsing all input.
   */
  virtual void finalize() {}
};

}  // namespace ethos

#endif /* STATE_H */
