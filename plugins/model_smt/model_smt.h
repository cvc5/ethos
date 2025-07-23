/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef SMT_MODEL_H
#define SMT_MODEL_H

#include <map>
#include <sstream>
#include <string>

#include "../std_plugin.h"

namespace ethos {

enum class DtKind
{
  EUNOIA_TERM,
  SMT_TERM,
  SMT_TYPE,
  SMT_VALUE,
  // these are required for native datatypes that define the semantics of
  // SMT-LIB
  VALUE_MAP,
  VALUE_STERM_LIST,
  VALUE_RAT_PAIR,
  NONE
  // a builtin application of an SMT-LIB operator
  // this is the kind of types of the form ($smt_apply_N ...)
  // BUILTIN_APPLY,
  // a builtin application of an SMT-LIB type operator
  // this is the kind of types of the form ($smt_type_N ...)
  // BUILTIN_TYPE
};
std::string dtKindToString(DtKind k);

/**
 * Used to generate a *.eo file that defines SMT-LIB model semantics.
 */
class ModelSmt : public StdPlugin
{
 public:
  ModelSmt(State& s);
  ~ModelSmt();
  /** */
  void bind(const std::string& name, const Expr& e) override;
  /** Finalize */
  void finalize() override;

 private:
  void addNormalSym(const std::string& sym,
                    const std::vector<Kind>& args,
                    Kind ret);
  void addSmtxSym(const std::string& sym,
                  const std::vector<Kind>& args,
                  const std::string& smtxName);
  void printModelEvalCallApp(const std::string& name,
                             const std::vector<Kind>& args,
                             std::ostream& os);
  void printType(const std::string& name, std::vector<Kind>& args);
  void printNormal(const std::string& name, std::vector<Kind>& args, Kind ret);
  void printSmtx(const std::string& name,
                 std::vector<Kind>& args,
                 Kind ret,
                 const std::string& smtxName);
  void printReduce(const std::string& name,
                   const std::vector<Kind>& args,
                   Kind ret,
                   const std::string& reduce);
  void finalizeDecl(const Expr& e);
  /** get the datatype e belongs to */
  DtKind getDtKind(const Expr& e);
  std::map<Kind, std::string> d_kindToEoPrefix;
  std::map<Kind, std::string> d_kindToEoCons;
  std::map<Kind, std::string> d_kindToType;
  std::map<std::string, std::string> d_overloadRevert;
  std::stringstream d_customEval;
  std::stringstream d_isValue;
  std::stringstream d_isType;
  std::stringstream d_typeEnum;
  std::stringstream d_constPred;
  std::stringstream d_modelEvalProgs;
  // SMT-LIB standard evaluation
  std::stringstream d_eval;
  /**
   * SMT-LIB symbols with "normal" evaluation, we give their argument kinds
   * and their return kind.
   */
  std::map<std::string, std::pair<std::vector<Kind>, Kind>> d_symNormal;
  /**
   * SMT-LIB symbols which have a $smtx_ utility function to compute them
   * natively.
   */
  std::map<std::string, std::tuple<std::vector<Kind>, Kind, std::string>>
      d_symSmtx;
  /**
   * SMT-LIB symbols that have simple reductions, we use x1 ... xn as references
   * to the arguments.
   */
  std::map<std::string, std::tuple<std::vector<Kind>, Kind, std::string>>
      d_symReduce;
};

}  // namespace ethos

#endif /* COMPILER_H */
