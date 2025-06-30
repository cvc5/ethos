/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef SMT_META_REDUCE_H
#define SMT_META_REDUCE_H

#include <map>
#include <set>
#include <sstream>
#include <string>

#include "expr_info.h"
#include "expr_trie.h"
#include "plugin.h"
#include "type_checker.h"

namespace ethos {

class State;
class TypeChecker;


enum class TermContextKind
{
  EUNOIA,
  SMT,
  SMT_BUILTIN,
  NONE
};
std::string termContextKindToString(TermContextKind k);

// TODO?
enum class TermKind
{
  //
  PROGRAM,
  // Builtin datatype introduced in model_smt step, for eo.Term
  EUNOIA_DT_CONS,
  // An internal-only symbol defined by the user
  EUNOIA_TERM,
  // The SMT-LIB term constructor for Eunoia
  EUNOIA_SMT_TERM_CONS,
  // SMT apply
  SMT_BUILTIN_APPLY,
  // Builtin datatype introduced in model_smt step, for sm.Term
  SMT_DT_CONS,
  // An SMT term defined by the user (possibly non-SMT-LIB standard)
  SMT_TERM,
  // The type of SMT lib terms
  SMT_TERM_TYPE,
  // ?
  EUNOIA_TERM_TYPE,
  // An operator that operates on native SMT-LIB terms, e.g. $eo_mk_binary
  EUNOIA_PROGRAM,
  // An operator that operates on native SMT-LIB terms, e.g. $sm_mk_pow2
  SMT_PROGRAM,
  // A term that was internal to model_smt step, should be removed
  INTERNAL,
  NONE
};
bool isEunoiaKind(TermKind tk);

std::string termKindToString(TermKind k);

class SelectorCtx
{
 public:
  SelectorCtx() {}
  /*
  SelectorCtx() : d_counter(0) {}
  std::string push(const std::string& next)
  {
    d_counter++;
    std::stringstream ss;
    ss << "z" << d_counter;
    d_letBegin << "(let ((z" << d_counter << " " << next << ")) ";
    d_letEnd << ")";
    return ss.str();
  }
  */
  std::map<Expr, std::string> d_ctx;
  /** The context it was matched in */
  std::map<Expr, TermContextKind> d_tctx;
  // std::stringstream d_letBegin;
  // std::stringstream d_letEnd;
  // size_t d_counter;
};

/**
 */
class SmtMetaReduce : public Plugin
{
 public:
  SmtMetaReduce(State& s);
  ~SmtMetaReduce();
  /** */
  void bind(const std::string& name, const Expr& e) override;
  /** Mark attributes */
  void markConstructorKind(const Expr& v, Attr a, const Expr& cons) override;
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Finalize */
  void finalize() override;

  /**
   */
  bool echo(const std::string& msg) override;

 private:
  void printConjunction(size_t n,
                        const std::string& conj,
                        std::ostream& os,
                        const SelectorCtx& ctx);
  bool printEmbPatternMatch(const Expr& c,
                            const std::string& initCtx,
                            std::ostream& os,
                            SelectorCtx& ctx,
                            size_t& nconj);
  void printEmbAtomicTerm(const Expr& c,
                          std::ostream& os,
                          TermContextKind tctx = TermContextKind::NONE);
  void printEmbType(const Expr& c, std::ostream& os);
  bool printEmbTerm(const Expr& c, std::ostream& os, const SelectorCtx& ctx);
  void finalizePrograms();
  void finalizeProgram(const Expr& v, const Expr& prog);
  void finalizeDeclarations();
  /** Does t have subterm s? */
  static bool hasSubterm(const Expr& t, const Expr& s);
  /** is smt apply, return the arity */
  size_t isSmtApply(const Expr& t,
                            bool& isType);
  /** is internal symbol? These dissappear in this step. */
  bool isInternalSymbol(const Expr& t);
  bool isProgram(const Expr& t);
  /** get term kind */
  TermKind getTermKindApply(const Expr& t,
                      std::string& name,
                      std::vector<Expr>& args,
                            bool& isType);
  TermKind getTermKind(const Expr& e, std::string& name);
  TermKind getTermKind(const Expr& e);
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  /** Declares seen */
  std::set<Expr> d_declSeen;
  /** Program declarations processed */
  std::set<Expr> d_progDeclProcessed;
  /** Programs seen */
  std::vector<std::pair<Expr, Expr>> d_progSeen;
  /** Attributes marked */
  std::map<Expr, std::pair<Attr, Expr>> d_attrDecl;
  /** Mapping expressions to strings */
  std::map<Expr, std::string> d_embMapAtomic;
  /** Common constants */
  Expr d_null;
  /** Number of current scopes. Bindings at scope>0 are not remembered */
  size_t d_nscopes;
  std::stringstream d_termDecl;
  std::stringstream d_eoTermDecl;
  std::stringstream d_defs;
  std::stringstream d_rules;
  std::stringstream d_smtVc;
  std::map<std::string, Kind> d_sufToKind;
  /** SMT-LIB indexed operators */
  std::map<std::string, size_t> d_indexedOperators;
  // SMT-LIB symbols
  bool d_inInitialize;
};

}  // namespace ethos

#endif /* COMPILER_H */
