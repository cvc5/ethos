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
 */
class SmtMetaReduce : public MetaReducePlugin
{
 public:
  SmtMetaReduce(State& s);
  ~SmtMetaReduce() override;
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Define */
  void define(const std::string& name, const Expr& e) override;
  /** Finalize */
  void finalize() override;
  /**
   */
  bool echo(const std::string& msg) override;

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
  bool isBuiltinMetaSymbol(const std::string& sname) const override;
  bool printEmbPatternMatch(const Expr& c,
                            const std::string& initCtx,
                            std::ostream& os,
                            SelectorCtx& ctx,
                            ConjPrint& print,
                            MetaKind tinit = MetaKind::NONE);
  void printEmbAtomicTerm(const Expr& c,
                          std::ostream& os,
                          MetaKind tctx = MetaKind::NONE);
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
  void finalizeDecl(const Expr& e) override;
  static std::string getEmbedName(const Expr& oApp);
  /** Program declarations processed */
  std::set<Expr> d_progDeclProcessed;
  std::stringstream d_defs;
  std::stringstream d_smtVc;
  // SMT-LIB term embedding
  std::stringstream d_embedTypeDt;
  std::stringstream d_embedTermDt;
  std::stringstream d_embedEoTermDt;
  std::stringstream d_embedValueDt;
  std::stringstream d_embedMapDt;
  std::stringstream d_embedSeqDt;
  /** */
  std::map<std::pair<Expr, size_t>, MetaKind> d_metaKindArg;
  /************* sygus *********/
  SmtMetaSygus d_smSygus;
};

}  // namespace ethos

#endif
