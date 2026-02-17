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

#include "../smt_meta/utils.h"
#include "../std_plugin.h"

namespace ethos {

class State;
class TypeChecker;

/**
 */
class LeanMetaReduce : public StdPlugin
{
 public:
  LeanMetaReduce(State& s);
  ~LeanMetaReduce();
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Define */
  void define(const std::string& name, const Expr& e) override;
  /** */
  void bind(const std::string& name, const Expr& e) override;
  /** Finalize */
  void finalize() override;
  /**
   */
  bool echo(const std::string& msg) override;

  bool printMetaType(const Expr& t,
                     std::ostream& os,
                     MetaKind tctx = MetaKind::NONE) const;
  /** Get the name of expression e, expected to be an atomic term */
  static std::string getName(const Expr& e);
  /** Is e a datatype constructor embedding? */
  static bool isEmbedCons(const Expr& e);
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
  MetaKind getMetaKind(State& s,
                       const Expr& e,
                       std::string& cname,
                       bool& isSmtTerm) const;

 private:
  MetaKind prefixToMetaKind(const std::string& str) const;
  void printEmbAtomicTerm(const Expr& c, std::ostream& os);
  bool printEmbTerm(const Expr& c,
                    std::ostream& os,
                    MetaKind tinit = MetaKind::NONE);
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
  void finalizeDecl(const Expr& e);
  static bool isProgram(const Expr& t);
  static bool isSmtApplyApp(const Expr& oApp);
  static std::string getEmbedName(const Expr& oApp);
  /** Common constants */
  Expr d_null;
  std::map<std::string, MetaKind> d_typeToMetaKind;
  std::stringstream d_defs;
  std::stringstream d_thms;
  /** Eunoia term embedding */
  std::stringstream d_embedTermDt;
  /** Eunoia to object inductive predicate */
  std::stringstream d_eoIsObj;
  /** Declares seen */
  std::set<Expr> d_declSeen;
  /** List of program definitions */
  std::vector<Expr> d_progDefs;
  std::map<Expr, Expr> d_progToDef;
  std::set<Expr> d_progIsDefine;
  /**
   */
  bool isProgramApp(const Expr& app);
  /**
   * Remove SMT-LIB identifier issues
   */
  static std::string cleanSmtId(const std::string& id);
  static std::string cleanId(const std::string& id);
};

}  // namespace ethos

#endif
