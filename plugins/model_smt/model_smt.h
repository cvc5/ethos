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
  void addHardCodeSym(const std::string& sym, const std::vector<Kind>& args);
  void addConstFoldSym(const std::string& sym,
                       const std::vector<Kind>& args,
                       Kind ret);
  void addLitBinSym(const std::string& sym,
                    const std::vector<Kind>& args,
                    const std::string& retWidth,
                    const std::string& retNum);
  void addLitSym(const std::string& sym,
                 const std::vector<Kind>& args,
                 Kind ret,
                 const std::string& retTerm);
  void addTermReduceSym(const std::string& sym,
                        const std::vector<Kind>& args,
                        const std::string& retTerm);
  void addReduceSym(const std::string& sym,
                    const std::vector<Kind>& args,
                    const std::string& retTerm);
  void addRecReduceSym(const std::string& sym,
                    const std::vector<Kind>& args,
                    const std::string& retTerm);
  void printModelEvalCallBase(const std::string& name,
                              const std::vector<Kind>& args,
                              const std::string& ret);
  void printModelEvalCall(const std::string& name,
                          const std::vector<Kind>& args);
  void printType(const std::string& name, const std::vector<Kind>& args);
  void printConstFold(const std::string& name,
                      const std::vector<Kind>& args,
                      Kind ret);
  void printLitReduce(const std::string& name,
                      const std::vector<Kind>& args,
                      Kind ret,
                      const std::string& reduce);
  void printAuxProgramCase(const std::string& name,
                           const std::vector<Kind>& args,
                           const std::string& ret,
                           size_t& paramCount,
                           std::ostream& progCases,
                           std::ostream& progParams);
  void printAuxProgram(const std::string& name,
                       const std::vector<Kind>& args,
                       std::stringstream& progCases,
                       std::stringstream& progParams);

  void printTermInternal(Kind k, const std::string& term, std::ostream& os);
  void finalizeDecl(const Expr& e);
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
  std::map<std::string, std::pair<std::vector<Kind>, Kind>> d_symConstFold;
  /**
   * SMT-LIB symbols that have simple reductions based on atomic arguments.
   */
  std::map<std::string, std::tuple<std::vector<Kind>, Kind, std::string>>
      d_symLitReduce;
  /**
   * SMT-LIB symbols that have simple term-level reductions, we use x1 ... xn as
   * references to the arguments.
   */
  std::map<std::string, std::pair<std::vector<Kind>, std::string>> d_symReduce;
  /**
   * SMT-LIB symbols that have a custom evaluation function that we define.
   */
  std::map<std::string, std::vector<Kind>> d_symHardCode;
};

}  // namespace ethos

#endif /* COMPILER_H */
