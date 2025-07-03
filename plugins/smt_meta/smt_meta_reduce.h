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

#include "../std_plugin.h"

namespace ethos {

class State;
class TypeChecker;


class ConjPrint
{
 public:
  ConjPrint();
  void push(const std::string& str);
  void printConjunction(std::ostream& os);
  std::stringstream d_ss;
  size_t d_npush;
};


/**
 * The datatype we are at.
 */
enum class TermContextKind
{
  EUNOIA,
  SMT,
  SMT_BUILTIN,
  SMT_TYPE,
  SMT_VALUE,
  PROGRAM,
  NONE
};
std::string termContextKindToString(TermContextKind k);
std::string termContextKindToPrefix(TermContextKind k);
std::string termContextKindToCons(TermContextKind k);

// TODO?
enum class TermKind
{
  FINAL_EUNOIA_TERM,
  FINAL_SMT_TERM,
  FINAL_SMT_TYPE,
  FINAL_SMT_VALUE,
  // these are required for native datatypes that define the semantics of
  // SMT-LIB
  FINAL_VALUE_MAP,
  FINAL_VALUE_STERM_LIST,
  FINAL_VALUE_RAT_PAIR,
  // a builtin application of an SMT-LIB operator
  // this is the kind of types of the form ($smt_apply_N ...)
  FINAL_BUILTIN_APPLY,
  // a builtin application of an SMT-LIB type operator
  // this is the kind of types of the form ($smt_type_N ...)
  FINAL_BUILTIN_TYPE,

  //
  PROGRAM,
  // Builtin datatype introduced in model_smt step, for eo.Term
  EUNOIA_DT_CONS,
  // An internal-only symbol defined by the user
  EUNOIA_TERM,
  // The SMT-LIB term constructor for Eunoia
  EUNOIA_SMT_TERM_CONS,
  EUNOIA_TYPE_TYPE,
  EUNOIA_QUOTE_TYPE,
  // SMT apply
  SMT_BUILTIN_APPLY,
  SMT_BUILTIN_APPLY_EQ,
  SMT_BUILTIN_TYPE,
  // Builtin datatype introduced in model_smt step, for sm.Term
  SMT_DT_CONS,
  // An SMT term defined by the user (possibly non-SMT-LIB standard)
  SMT_TERM,
  // The type of SMT lib terms
  SMT_TERM_TYPE,
  // The type of SMT lib types
  SMT_TYPE_TYPE,
  SMT_TYPE_DT_CONS,
  // An SMT-LIB standard type that is associated with a literal Kind
  SMT_STD_TYPE,
  // ?
  EUNOIA_TERM_TYPE,
  EUNOIA_BOOL,
  // An operator that operates on native SMT-LIB terms, e.g. $eo_mk_binary
  SMT_TO_EO_PROGRAM,
  SMT_PROGRAM,
  // An operator that operates on native SMT-LIB terms, e.g. $sm_mk_pow2
  SMT_BUILTIN_PROGRAM,
  // A term that was internal to model_smt step, should be removed
  INTERNAL,
  NONE
};
bool isEunoiaKind(TermKind tk);

std::string termKindToString(TermKind k);

class SelectorCtx
{
 public:
  SelectorCtx();
  void clear();
  /** */
  std::map<Expr, std::string> d_ctx;
  /** The context it was matched in */
  std::map<Expr, TermContextKind> d_tctx;
  /**
   * The term it was matched to
   */
  std::map<Expr, Expr> d_typeMatch;
};

/**
 */
class SmtMetaReduce : public StdPlugin
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
                                         ConjPrint& print,
                            size_t& nconj,
                            TermContextKind tinit = TermContextKind::NONE);
  void printEmbAtomicTerm(const Expr& c,
                          std::ostream& os,
                          TermContextKind tctx = TermContextKind::NONE);
  TermKind printEmbType(const Expr& c,
                        std::ostream& os,
                        TermContextKind tctx = TermContextKind::NONE);
  bool printEmbTerm(const Expr& c,
                    std::ostream& os,
                    const SelectorCtx& ctx,
                    TermContextKind tinit = TermContextKind::NONE);
  void finalizePrograms();
  void finalizeProgram(const Expr& v, const Expr& prog);
  void finalizeDeclarations();
  /** Does t have subterm s? */
  static bool hasSubterm(const Expr& t, const Expr& s);
  /** is smt apply, return the arity */
  TermKind isSmtApply(const Expr& t);
  bool isProgramKind(TermKind tk);
  bool isProgram(const Expr& t);
  /** get term kind */
  TermKind getTermKindApply(const Expr& t,
                            std::string& name,
                            std::vector<Expr>& args);
  TermKind getTermKindAtomic(const Expr& e, std::string& name);
  TermKind getTermKind(const Expr& e, std::string& name);
  TermKind getTermKind(const Expr& e);

  /** */
  TermContextKind getMetaKind(const Expr& e);

  TermContextKind termKindToContext(TermKind tk);
  TermContextKind getEmbTypeContext(const Expr& type);
  std::string getName(const Expr& e);
  std::string getEmbedName(const Expr& oApp);
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
  std::stringstream d_termDecl;
  std::stringstream d_typeDecl;
  std::stringstream d_eoTermDecl;
  std::stringstream d_defs;
  std::stringstream d_rules;
  std::stringstream d_smtVc;
  // TODO: maybe not necessary?
  std::map<Expr, std::vector<TermKind>> d_metaType;
  /** The Eunoia program that returns the meta-kind of terms */
  Expr d_eoGetMetaKind;
  Expr d_metaEoTerm;
  Expr d_metaSmtTerm;
  Expr d_metaSmtType;
  Expr d_metaSmtBuiltinType;
  Expr d_metaSmtValue;
  /** */
  std::map<Expr, TermContextKind> d_metaKind;
  std::map<std::pair<Expr, size_t>, TermContextKind> d_metaKindArg;
  /**
   */
  TermContextKind getTypeMetaKind(const Expr& typ);
  /**
   */
  bool isProgramApp(const Expr& app);
  /**
   * This returns the expected meta-kind for the i^th child of
   * parent. It should not depend on parent[i] at all.
   */
  TermContextKind getMetaKindArg(const Expr& parent, size_t i);
  /**
   * Returns the result of calling the above method for all
   * children i of parent.
   */
  std::vector<TermContextKind> getMetaKindArgs(const Expr& parent);
  /**
   * Get the meta-kind returned by a child.
   */
  TermContextKind getMetaKindReturn(const Expr& child);
  /**
   * Same as above, but collects (flattens) the arguments of APPLY
   */
  TermContextKind getMetaKindReturn(const Expr& child,
  std::vector<Expr>& appArgs);
};

}  // namespace ethos

#endif /* COMPILER_H */
