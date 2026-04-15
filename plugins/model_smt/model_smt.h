/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_MODEL_SMT_H
#define PLUGIN_MODEL_SMT_H

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
  /**
   * The following functions are used to setup auto-generation of cases
   * to add to $smtx_model_eval. In all cases, we provide an argument
   * kind vector to determine the expected signature of the operator,
   * which determines how to pattern match on it.
   */
  /**
   * Add function whose evaluation is <retTerm>.
   */
  void addReduceSym(const std::string& sym,
                    const std::vector<Kind>& args,
                    Kind ret,
                    const std::string& retTerm);
  /**
   * Add function whose evaluation is ($smt_model_eval <retTerm>).
   */
  void addTermReduceSym(const std::string& sym,
                        const std::vector<Kind>& args,
                        Kind ret,
                        const std::string& retTerm);
  /**
   * Add function that should be eliminated in the Eunoia to SMT-LIB term
   * layer.
   */
  void addEunoiaReduceSym(const std::string& sym,
                          const std::vector<Kind>& args,
                          const std::string& retTerm,
                          bool isType = false);
  /**
   * Add function whose evaluation is
   * (eo::define ((e1 ($smt_model_eval x1)))
   * (eo::define ((e2 ($smt_model_eval x2)))
   *  <retTerm>)).
   */
  void addRecReduceSym(const std::string& sym,
                       const std::vector<Kind>& args,
                       Kind ret,
                       const std::string& retTerm);
  /**
   * Add function whose evaluation is
   * ($smt_model_eval_<sym> ($smt_model_eval x1) ($smt_model_eval x2)),
   * where $smt_model_eval_<sym> is manually defined program.
   */
  void addHardCodeSym(const std::string& sym, const std::vector<Kind>& args);
  /**
   * Add function whose evaluation is given by
   * ($smt_model_eval_<sym> ($smt_model_eval x1) ($smt_model_eval x2)),
   * where $smt_model_eval_<sym> is an auto-generated auxiliary
   * program whose case is determined by args, and has <retTerm> as its
   * return, e.g.:
   * (program $smt_model_eval_<sym> ()
   *   :signature ($smt_Value $smt_Value) $smt_Value
   *   (
   *   (($smt_model_eval_<sym> ($eo_<arg1> x1) ($eo_<arg2> x2)) <retTerm>)
   *   )
   * )
   * Note that x1, ..., xn in this context are SMT-LIB literal values.
   */
  void addLitSym(const std::string& sym,
                 const std::vector<Kind>& args,
                 Kind ret,
                 const std::string& retTerm);
  /**
   * Similar to addLitSym, but where <retTerm> is
   * ($vsm_term ($sm_mk_binary <retWidth> <retNum>)).
   */
  void addLitBinSym(const std::string& sym,
                    const std::vector<Kind>& args,
                    const std::string& retWidth,
                    const std::string& retNum,
                    bool reqSameWidth = true);
  /**
   * Similar to addLitSym, but where <retTerm> is
   * automatically generated for sym, args, ret to invoke the
   * SMT-LIB operator. For example, if sym is "and", args is {Kind::BOOL,
   * Kind::BOOL}, and ret is Kind::BOOL, then <retTerm> is
   * ($vsm_term ($sm_mk_bool ($native_apply_2 "and" x1 x2))).
   * The return kind determines which $sm_mk_* in the return,
   * and the argument kinds determine
   */
  void addConstFoldSym(const std::string& sym,
                       const std::vector<Kind>& args,
                       Kind ret);
  /** add type */
  void addTypeSym(const std::string& sym, const std::vector<Kind>& args);
  /** add symbol case */
  void addSymCase(const std::string& sym,
                  const std::string& pat,
                  const std::string& ret);
  void printEvalCallBase(std::ostream& out,
                         const std::string& mname,
                         const std::string& name,
                         const std::vector<Kind>& args,
                         const std::string& ret);
  /**
   * Helper method for printing the final program case to $smtx_model_eval, i.e.
   * (($smtx_model_eval (<name> x1 ... xn)) <retTerm>).
   */
  void printModelEvalCallBase(const std::string& name,
                              const std::vector<Kind>& args,
                              const std::string& ret);
  /**
   * Helper method for printing the final program case to $smtx_model_eval, i.e.
   * (($eo_to_smt (<name> x1 ... xn)) <retTerm>).
   */
  void printEunoiaReduce(const std::string& name,
                         const std::vector<Kind>& args,
                         const std::string& ret);
  /**
   * Same as printModelEvalCallBase, but where <retTerm> is
   * ($smtx_model_eval_<name> ($smtx_model_eval x1) ... ($smtx_model_eval xn)).
   */
  void printModelEvalCall(const std::string& name,
                          const std::vector<Kind>& args);
  /** Print necessary information for a symbol added via addConstFoldSym */
  void printConstFold(const std::string& name,
                      const std::vector<Kind>& args,
                      Kind ret);
  /** Print necessary information for a symbol added via addTermReduceSym */
  void printTermReduce(const std::string& name,
                       const std::vector<Kind>& args,
                       const std::string& ret);
  /** Print necessary information for a symbol added via addLitSym */
  void printLitReduce(const std::string& name,
                      const std::vector<Kind>& args,
                      Kind ret,
                      const std::string& reduce);
  /** Print for type */
  void printDecl(const std::string& name,
                 const std::vector<Kind>& args,
                 Kind ret = Kind::PARAM,
                 size_t nopqArgs = 0);
  void printAuxProgramCase(const std::string& name,
                           const std::vector<Kind>& args,
                           const std::string& ret,
                           size_t& paramCount,
                           std::ostream& progCases,
                           std::ostream& progParams,
                           bool isTypeProg = false);
  void printAuxProgram(const std::string& name,
                       const std::vector<Kind>& args,
                       std::stringstream& progCases,
                       std::stringstream& progParams);
  void printAuxTypeProgram(const std::string& name,
                           const std::vector<Kind>& args,
                           const std::string& retType,
                           std::stringstream& out);
  void addAuxTypeProgram(const std::string& name,
                           const std::vector<Kind>& args,
                           const std::string& retType);
  /** Add eo_is_list_nil aux definition */
  void addAuxIsListNil(const std::string& name, const std::string& ret);
  /**
   * Print program where zeroRet and succRet should use parameters
   * n, v1 .... vm, where n is the predecessor Nat (only used in succRet)
   * and v1 ... vm are smt values.
   */
  void printAuxNatRecProgram(const std::string& name,
                             const std::vector<Kind>& args,
                             const std::string& zeroRet,
                             const std::string& succRet);
  void printTypeof(const std::string& name,
                   const std::vector<Kind>& args,
                   Kind ret);

  void printTermInternal(Kind k, const std::string& term, std::ostream& os);
  /** Finalize declaration, main entry point for calling methods above */
  void finalizeDecl(const std::string& name, const Expr& e);
  /** Utilities for determining how to print arguments and returns */
  std::map<Kind, std::string> d_kindToEoPrefix;
  std::map<Kind, std::string> d_kindToEoCons;
  std::map<Kind, std::string> d_kindToType;
  std::map<std::string, std::string> d_overloadRevert;
  std::map<std::string, std::string> d_overloadRevertRev;
  std::map<std::string, size_t> d_opqArgs;
  Expr d_null;
  /** Auxiliary programs for SMT-LIB model evaluation */
  std::stringstream d_modelEvalProgsFwd;
  std::stringstream d_modelEvalProgs;
  /** SMT-LIB model evaluation cases */
  std::stringstream d_eval;
  /** Conversion Eunoia to SMT */
  std::stringstream d_eoToSmt;
  std::stringstream d_eoToSmtType;
  std::stringstream d_eoToSmtAux;
  /** Term and type constructors */
  std::stringstream d_smtTerms;
  std::stringstream d_smtTypes;
  /** SMT type rules for terms */
  std::stringstream d_smtTypeof;
  std::stringstream d_smtTypeofAux;
  /** Desugar aux */
  std::stringstream d_desugarAux;
  /** Declarations seen */
  std::vector<std::pair<std::string, Expr>> d_declSeen;
  /** Special cases, printed prior to symbol */
  std::map<std::string, std::vector<std::pair<std::string, std::string>>>
      d_specialCases;
  /** Auxiliary definitions on $EO_TO_SMT_AUX$ */
  std::map<std::string, std::string> d_auxDef;
  /** Auxiliary definitions on $SMT_EVAL_PROGS$ */
  std::map<std::string, std::string> d_auxSmtEval;
  /** Auxiliary definitions of nil terminator recognizers */
  std::map<std::string, std::string> d_auxDesugar;
  /** SMT-LIB types. */
  std::map<std::string, std::vector<Kind>> d_symTypes;
  //--------
  /** special case for eo_to_smt return, for smt supported symbols */
  std::map<std::string, std::string> d_eoToSmtFullCase;
  //-------- for defining SMT term type rules
  /** Special cases: d_typeCase is an auxiliary program which will be called */
  std::map<std::string, std::string> d_typeCase;
  /** Specifies a SmtType to fill in as the return */
  std::map<std::string, std::string> d_typeRetCase;
  /** Specifies a custom return from $smtx_typeof */
  std::map<std::string, std::string> d_typeFullCase;
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
  std::map<std::string, std::tuple<std::vector<Kind>, Kind, std::string>>
      d_symReduce;
  /** those marked rec reduce */
  std::unordered_set<std::string> d_recReduce;
  /**
   * Eunoia terms that have special reductions to SMT-LIB terms
   */
  std::map<std::string, std::pair<std::vector<Kind>, std::string>>
      d_eoSymReduce;
  // subset of those that are types
  std::unordered_set<std::string> d_eoSymReduceTypes;
  /** Symbols that we need no definition for */
  std::map<std::string, bool> d_symIgnore;
  /** SMT-LIB syntax to embedding helper */
  static std::string smtToSmtEmbed(const std::string& str, bool isTerm = false);
  static std::string smtBinaryBinReturn(const std::string& term);
  static std::string smtEval(const std::string& s);
  static std::string eoDefine(const std::string& x,
                              const std::string& t,
                              const std::string& ret);
  /** Print type internal */
  bool printTypeInternal(const std::string& name, Kind k, std::ostream& out);
  /** Kinds */
  Kind d_kSet;
  Kind d_kArray;
  Kind d_kSeq;
  Kind d_kBit;
  Kind d_kIntQuote;
};

}  // namespace ethos

#endif
