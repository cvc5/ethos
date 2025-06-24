/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef DESUGAR_H
#define DESUGAR_H

#include <map>
#include <set>
#include <sstream>
#include <string>

#include "plugin.h"
#include "expr_info.h"
#include "expr_trie.h"
#include "type_checker.h"

namespace ethos {

class State;
class TypeChecker;

/**
 */
class Desugar : public Plugin
{
  friend class TypeChecker;
public:
  Desugar(State& s);
  ~Desugar();
  /** Intialize */
  void initialize() override;
  /** Reset */
  void reset() override;
  /** Push scope */
  void pushScope() override;
  /** Pop scope */
  void popScope() override;
  /** include file, if not already done */
  void includeFile(const Filepath& s, bool isReference, const Expr& referenceNf) override;
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t) override;
  /** */
  void bind(const std::string& name, const Expr& e) override;
  /** Mark attributes */
  void markConstructorKind(const Expr& v, Attr a, const Expr& cons) override;
  /** Mark oracle command */
  void markOracleCmd(const Expr& v, const std::string& ocmd) override;
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Finalize */
  void finalize() override;
  /** To string, which returns the smt2 formalization of the meta-level correctness of the signature */
  std::string toString();
private:
  void printTerm(const Expr& e, std::ostream& os);
  void printParamList(const std::vector<Expr>& vars, std::ostream& os, std::vector<Expr>& params, bool useImplicit);
  void printParamList(const std::vector<Expr>& vars, std::ostream& os, std::vector<Expr>& params, bool useImplicit, std::map<Expr, bool>& visited, bool& firstParam, bool isOpaque=false);
  void finalizeSetLiteralTypeRule(Kind k, const Expr& t);
  void finalizeProgram(const Expr& v, const Expr& prog);
  void finalizeDefinition(const std::string& name, const Expr& t);
  void finalizeDeclaration(const Expr& t);
  void finalizeRule(const Expr& v);
  void finalizeDatatype(const Expr& d);
  /** Does t have subterm s? */
  static bool hasSubterm(const Expr& t, const Expr& s);
  /** */
  Expr mkSanitize(const Expr& t, std::vector<Expr>& vars);
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  /** Declares seen */
  std::vector<std::pair<Expr, Kind>> d_declSeen;
  /** Attributes marked */
  std::map<Expr, std::pair<Attr, Expr>> d_attrDecl;
  /** Declares processed */
  std::set<Expr> d_declProcessed;
  /** */
  Expr d_eoTmpInt;
  Expr d_eoTmpNil;
  /** Common constants */
  Expr d_null;
  Expr d_listNil;
  Expr d_listCons;
  Expr d_listType;
  /** Number of current scopes. Bindings at scope>0 are not remembered */
  size_t d_nscopes;
  
  class ProgramOut
  {
  public:
    ProgramOut() : d_firstParam(true) {}
    bool d_firstParam;
    std::map<Expr, bool> d_visited;
    std::stringstream d_out;
    std::stringstream d_param;
    std::vector<Expr> d_params;
  };

  std::stringstream d_numDecl;
  std::stringstream d_num;
  std::stringstream d_defs;
  std::stringstream d_eoNilNground;
  std::stringstream d_eoNil;
  ProgramOut d_eoTypeof;
  ProgramOut d_eoDtCons;
  ProgramOut d_eoDtSel;
  std::stringstream d_eoRules;
};

}  // namespace ethos

#endif /* COMPILER_H */
