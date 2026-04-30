/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_SMT_META_REDUCE_H
#define PLUGIN_SMT_META_REDUCE_H

#include <map>
#include <set>
#include <string>

#include "../meta_reduce_plugin.h"
#include "smt_meta_sygus.h"

namespace ethos {

class State;
class TypeChecker;

/**
 * Plugin that lowers generated EO into the SMT-LIB meta encoding.
 *
 * The SMT meta-reduction stage consumes the desugared/model_smt EO layer and
 * emits an SMT-LIB file that deep-embeds Eunoia terms, SMT terms, SMT types,
 * SMT values, maps, and sequences.  It uses the same `MetaKind`
 * classification as the Lean backend, but prints datatype constructors and
 * program definitions in the SMT-LIB template language.
 *
 * Generated proof-rule VCs become satisfiability queries over the syntactic
 * space of embedded Eunoia terms.  When enabled, the companion SyGuS helper
 * receives the same declarations so an alternate grammar can be emitted.
 */
class SmtMetaReduce : public MetaReducePlugin
{
 public:
  /** Construct the SMT meta reducer and initialize optional SyGuS support. */
  SmtMetaReduce(State& s);
  /** Destroy the SMT meta reducer. */
  ~SmtMetaReduce() override;
  /** Remember a program definition for later SMT-LIB emission. */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Convert supported define commands into program definitions. */
  void define(const std::string& name, const Expr& e) override;
  /** Emit the generated SMT-LIB meta file. */
  void finalize() override;
  /** Interpret SMT-meta control echo commands. */
  bool echo(const std::string& msg) override;

  /** Print the SMT-LIB sort corresponding to EO type t. */
  bool printMetaType(const Expr& t,
                     std::ostream& os,
                     MetaKind tctx = MetaKind::NONE) const;
  using MetaReducePlugin::getName;
  using MetaReducePlugin::isEmbedCons;
  /**
   * Return the "meta-kind" of a type typ, based on its naming convention
   * introduced in the model_smt layer. In other words, we return the datatype
   * that typ represents if applicable, SMT_BUILTIN if typ refers to a builtin
   * SMT-LIB type, or elseKind otherwise.
   * @param typ The given type.
   * @param elseKind The returned kind if typ does not have a special meaning.
   * @return The meta-kind of typ, or elseKind otherwise.
   */
  MetaKind getTypeMetaKind(const Expr& typ,
                           MetaKind elseKind = MetaKind::EUNOIA) const;
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
  /** Return true if sname denotes an SMT meta symbol supplied by templates. */
  bool isBuiltinMetaSymbol(const std::string& sname) const override;
  /** Print a selector-sensitive embedded pattern match. */
  bool printEmbPatternMatch(const Expr& c,
                            const std::string& initCtx,
                            std::ostream& os,
                            SelectorCtx& ctx,
                            ConjPrint& print,
                            MetaKind tinit = MetaKind::NONE);
  /** Print an atomic EO expression in the SMT-LIB embedding. */
  void printEmbAtomicTerm(const Expr& c,
                          std::ostream& os,
                          MetaKind tctx = MetaKind::NONE);
  /** Print an EO expression as an SMT-LIB embedded term. */
  bool printEmbTerm(const Expr& c,
                    std::ostream& os,
                    const SelectorCtx& ctx,
                    MetaKind tinit = MetaKind::NONE);
  /**
   * Write program definition to d_defs. For consistency this is also called
   * for define commands.
   * @param v The program variable.
   * @param prog The program definition.
   * @param isDefine True iff this program definition originated from a
   * define command.
   */
  void finalizeProgram(const Expr& v, const Expr& prog, bool isDefine = false);
  /** Emit a declaration into the appropriate SMT-LIB embedded datatype. */
  void finalizeDecl(const Expr& e) override;
  /** Return the SMT-LIB constructor name for an embedded SMT operator. */
  static std::string getEmbedName(const Expr& oApp);
  /** Program declarations processed */
  std::set<Expr> d_progDeclProcessed;
  /** Generated SMT-LIB program definitions. */
  std::stringstream d_defs;
  /** Generated SMT-LIB VC assertions and commands. */
  std::stringstream d_smtVc;
  /** SMT-LIB type embedding datatype cases. */
  std::stringstream d_embedTypeDt;
  /** SMT-LIB term embedding datatype cases. */
  std::stringstream d_embedTermDt;
  /** Eunoia term embedding datatype cases. */
  std::stringstream d_embedEoTermDt;
  /** SMT value embedding datatype cases. */
  std::stringstream d_embedValueDt;
  /** SMT map embedding datatype cases. */
  std::stringstream d_embedMapDt;
  /** SMT sequence embedding datatype cases. */
  std::stringstream d_embedSeqDt;
  /** Per-argument meta-kind overrides for embedded constructors. */
  std::map<std::pair<Expr, size_t>, MetaKind> d_metaKindArg;
  /** Helper that mirrors declarations for optional SyGuS output. */
  SmtMetaSygus d_smSygus;
};

}  // namespace ethos

#endif
