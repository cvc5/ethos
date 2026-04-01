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
 */
class LeanMetaReduce : public MetaReducePlugin
{
 public:
  LeanMetaReduce(State& s);
  ~LeanMetaReduce() override;
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
  bool printMetaTypeKind(MetaKind k, std::ostream& os) const;
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
  bool isBuiltinMetaSymbol(const std::string& sname) const override;
  void printEmbAtomicTerm(const Expr& c, std::ostream& os);
  void printEmbTerm(const Expr& c,
                    std::ostream& os,
                    MetaKind tinit = MetaKind::NONE,
                    bool maybeLetify = true);
  void printEmbTermInternal(const Expr& c,
                            std::ostream& os,
                            MetaKind tinit,
                            std::map<const ExprValue*, size_t>& lbind);
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
  void finalizeDecl(const Expr& e) override;
  static bool isProgram(const Expr& t);
  void finalizeChecker();
  void finalizeSmtModel();
  void finalizeSpec();
  void finalizeLemmas();
  /**
   * ctx impacts __eo_lit vs. __smt_lit
   */
  static std::string getEmbedName(const Expr& oApp,
                                  MetaKind ctx = MetaKind::EUNOIA);
  std::stringstream d_defs;
  std::stringstream d_eoIsObjDefs;
  std::stringstream d_thms;
  /** Eunoia term embedding */
  std::stringstream d_embedTermDt;
  /** Eunoia to object inductive prop */
  std::stringstream d_eoIsObj;
  /** Eunoia is refutation prop */
  std::stringstream d_eoIsRef;
  /** */
  std::stringstream d_eoChecker;
  /** SMT definitions */
  std::stringstream d_smtDefs;
  std::stringstream d_smt;
  std::stringstream d_smtDt;
  std::stringstream d_smtTypeDt;
  std::stringstream d_smtValueDt;
  std::stringstream d_cmdDt;
  std::stringstream d_ruleDt;
  std::stringstream d_lemmaAuxDef;
  /** List of program definitions */
  std::vector<Expr> d_progDefs;
  std::map<Expr, Expr> d_progToDef;
  std::set<Expr> d_progIsDefine;
  /**
   * Remove SMT-LIB identifier issues
   */
  static std::string cleanSmtId(const std::string& id);
  static std::string cleanId(const std::string& id);
};

}  // namespace ethos

#endif
