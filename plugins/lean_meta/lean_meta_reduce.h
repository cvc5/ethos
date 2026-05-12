/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_LEAN_META_REDUCE_H
#define PLUGIN_LEAN_META_REDUCE_H

#include <map>
#include <set>
#include <sstream>
#include <string>

#include "../meta_reduce_plugin.h"

namespace ethos {

class State;
class TypeChecker;

/**
 * Plugin that lowers generated EO into a Lean meta-theory file.
 *
 * The Lean meta-reduction stage consumes the desugared/model_smt EO layer and
 * emits Lean definitions for the deep embedding used by proof-rule checking:
 * Eunoia terms and proofs, SMT terms/types/values, checker commands, rules,
 * and the generated programs that connect them.  It follows the naming
 * conventions introduced by desugar and model_smt to classify expressions by
 * `MetaKind`, then prints each EO expression as a Lean term of the
 * corresponding embedded datatype.
 *
 * This stage is the Lean analogue of smt_meta_reduce: instead of producing an
 * SMT-LIB conjecture, it writes Lean definitions, specifications, checker
 * infrastructure, and lemmas that Lean can typecheck and prove terminating.
 */
class LeanMetaReduce : public MetaReducePlugin
{
 public:
  /** Construct the Lean meta reducer and its meta-kind tables. */
  LeanMetaReduce(State& s);
  /** Destroy the Lean meta reducer. */
  ~LeanMetaReduce() override;
  /** Remember a program definition for later Lean emission. */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Convert supported define commands into program definitions. */
  void define(const std::string& name, const Expr& e) override;
  /** Emit the generated Lean meta-theory file. */
  void finalize() override;
  /** Interpret Lean-meta control echo commands. */
  bool echo(const std::string& msg) override;

  /** Print the Lean type corresponding to EO type t. */
  bool printMetaType(const Expr& t,
                     std::ostream& os,
                     MetaKind tctx = MetaKind::NONE) const;
  /** Print the Lean type name corresponding to a meta-kind. */
  bool printMetaTypeKind(MetaKind k, std::ostream& os) const;
  using MetaReducePlugin::getName;
  using MetaReducePlugin::isEmbedCons;
  /**
   * Return the "meta-kind" of a type typ, based on its naming convention
   * introduced in the model_smt layer. In other words, we return the datatype
   * that typ represents if applicable, SMT_BUILTIN if typ refers to a
   * builtin SMT-LIB type, or EUNOIA otherwise.
   * @param typ The given type.
   * @return The meta-kind of typ, or EUNOIA otherwise.
   */
  MetaKind getTypeMetaKind(const Expr& typ) const;
  /**
   * Get the meta kind of the type of expression e, or else kind otherwise.
   * In other words, we return the datatype that e is a constructor of in the
   * final embedding, SMT_BUILTIN if e is a builtin SMT-LIB application, or
   * elseKind otherwise.
   * @param s Reference to the state
   * @param e The given expression.
   * @param cname Updated to the root name of the constructor.
   * @return The meta-kind of the type of e, or elseKind otherwise.
   */
  MetaKind getMetaKind(State& s, const Expr& e, std::string& cname) const;

 private:
  /** Return true if sname denotes a Lean meta symbol supplied by templates. */
  bool isBuiltinMetaSymbol(const std::string& sname) const override;
  /** Print an atomic EO expression in the Lean embedding. */
  void printEmbAtomicTerm(const Expr& c, std::ostream& os);
  /** Print an EO expression as a Lean embedded term. */
  void printEmbTerm(const Expr& c,
                    std::ostream& os,
                    MetaKind tinit = MetaKind::NONE,
                    bool maybeLetify = true);
  /** Recursive implementation of printEmbTerm with let-binding state. */
  void printEmbTermInternal(const Expr& c,
                            std::ostream& os,
                            MetaKind tinit,
                            std::map<const ExprValue*, size_t>& lbind);
  /** Emit all remembered program definitions. */
  void finalizePrograms();
  /**
   * Write program definition to d_defs. For consistency this is also called
   * for define commands.
   * @param v The program variable.
   * @param prog The program definition.
   * @param isDefine True iff this program definition originated from a
   * define command.
   */
  void finalizeProgram(const Expr& v, const Expr& prog, bool isDefine = false);
  /** Emit a declaration into the appropriate Lean embedded datatype. */
  void finalizeDecl(const Expr& e) override;
  /** Return whether t is a program type or program constant. */
  static bool isProgram(const Expr& t);
  /** Emit the Lean checker definitions. */
  void finalizeChecker();
  /** Emit Lean definitions for the SMT model layer. */
  void finalizeSmtModel();
  /** Emit Lean specifications for generated proof-rule targets. */
  void finalizeSpec();
  /** Emit Lean lemma scaffolding for generated specifications. */
  void finalizeLemmas();
  /**
   * Return the Lean symbol name for an embedded SMT operator.
   */
  static std::string getEmbedName(const Expr& oApp,
                                  MetaKind ctx = MetaKind::EUNOIA);
  /** Print one checker step include case. */
  void printStepCase(std::ostream& out, const std::string& str, bool isPop);
  /** Print the empty checker step include case. */
  void printStepEmptyCase(std::ostream& out,
                          const std::string& str,
                          bool isPop);
  /** Return true if c can be printed as an atomic Eunoia term. */
  bool isAtomicEo(const Expr& c, const std::string& cname, size_t& uarity);
  /** Return true if c can be printed as an atomic SMT term. */
  bool isAtomicSmt(const Expr& c, const std::string& cname);
  /** Generated Lean definitions for programs. */
  std::stringstream d_defs;
  /** Generated mutually recursive total Lean definitions. */
  std::stringstream d_defsTotal;
  /** Whether any generated definitions have been seen. */
  bool d_hasDefs;
  /** Generated helper definitions for Eunoia-object membership. */
  std::stringstream d_eoIsObjDefs;
  /** Eunoia term embedding */
  std::stringstream d_embedTermDt;
  /** Eunoia operator embedding */
  std::stringstream d_embedTOpDt[4];
  /** Eunoia to object inductive prop */
  std::stringstream d_eoIsObj;
  /** Eunoia is refutation prop */
  std::stringstream d_eoIsRef;
  /** Generated Lean checker body. */
  std::stringstream d_eoChecker;
  /** SMT definitions */
  std::stringstream d_smtDefs;
  /** Generated Lean SMT helper definitions. */
  std::stringstream d_smt;
  /** SMT term datatype cases. */
  std::stringstream d_smtDt;
  /** SMT theory-operator datatype cases. */
  std::stringstream d_smtTOpDt;
  /** SMT type datatype cases. */
  std::stringstream d_smtTypeDt;
  /** SMT value datatype cases. */
  std::stringstream d_smtValueDt;
  /** Checker command datatype cases. */
  std::stringstream d_cmdDt;
  /** Checker rule datatype cases. */
  std::stringstream d_ruleDt;
  /** Rule include cases. */
  std::stringstream d_rlInclude;
  /** Checker step include cases. */
  std::stringstream d_rlIncludeStep;
  /** Checker step-pop include cases. */
  std::stringstream d_rlIncludeStepPop;
  /** List of program definitions */
  std::vector<Expr> d_progDefs;
  /** Map from each program symbol to its definition. */
  std::map<Expr, Expr> d_progToDef;
  /** Programs that originated from define commands. */
  std::set<Expr> d_progIsDefine;
  /** Programs inferred to require total definitions. */
  std::set<Expr> d_totalDefProgs;
  /** Return a Lean-safe version of an SMT-LIB identifier. */
  static std::string cleanSmtId(const std::string& id);
  /** Return a Lean-safe version of a general generated identifier. */
  static std::string cleanId(const std::string& id);
};

}  // namespace ethos

#endif
