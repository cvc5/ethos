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
#include <tuple>
#include <unordered_set>
#include <vector>

#include "../std_plugin.h"
#include "eo_reduce_spec.h"

namespace ethos {

/**
 * Plugin that generates the EO layer for SMT-LIB model semantics.
 *
 * model_smt consumes the desugared EO signature and emits
 * `model_smt_gen.eo`, which defines `$eo_model_sat` and the supporting
 * model-evaluation machinery used by later SMT/Lean meta encoders.  It maps
 * Eunoia constants to SMT-LIB terms, types, and values, generates datatype
 * constructors for the deep embedding, and adds evaluation/typeof cases for
 * supported SMT-LIB operators.
 *
 * The operator tables initialized by this class are part of the trusted
 * semantic bridge from Eunoia syntax to SMT-LIB behavior.  Unknown user
 * symbols are rejected during finalization rather than silently modeled as
 * uninterpreted symbols.
 *
 * The symbols that have no SMT-LIB semantics of their own, because they are
 * eliminated on the way to the SMT-LIB term layer, are not part of those
 * tables: they are read from a Eunoia reduction file that gives their case of
 * `$eo_to_smt` resp. `$eo_to_smt_type` directly, see loadReduceSpec.
 */
class ModelSmt : public StdPlugin
{
 public:
  /** Construct the model_smt plugin and register supported SMT operators. */
  ModelSmt(State& s);
  /** Destroy the model_smt plugin. */
  ~ModelSmt();
  /** Remember constant declarations for model-semantics generation. */
  void bind(const std::string& name, const Expr& e) override;
  /** Emit the generated EO file containing SMT-LIB model semantics. */
  void finalize() override;

 private:
  /**
   * Registration helpers for auto-generated `$smtx_model_eval` cases.
   *
   * Each helper records an operator name together with argument/return kinds.
   * The kind vector determines both the generated EO pattern and the expected
   * SMT-LIB literal/value shape used by the corresponding printer.
   */
  /**
   * Add function whose evaluation is <retTerm>.
   */
  void addReduceSym(const std::string& sym,
                    const std::vector<Kind>& args,
                    Kind ret,
                    const std::string& retTerm);
  /**
   * Add function whose evaluation is ($smtx_model_eval <retTerm>).
   */
  void addTermReduceSym(const std::string& sym,
                        const std::vector<Kind>& args,
                        Kind ret,
                        const std::string& retTerm);
  /**
   * Read the Eunoia-to-SMT reduction file at resourcePath, which specifies the
   * symbols that are eliminated in the Eunoia to SMT-LIB term layer, i.e. that
   * get a case of $eo_to_smt or $eo_to_smt_type of their own instead of a
   * constructor and an SMT-LIB semantics. See EoReduceSpec and, for the
   * format, the header comment of plugins/model_smt/eo_to_smt_cpc.eo.
   */
  void loadReduceSpec(const std::string& resourcePath);
  /**
   * Add function whose evaluation is
   * (eo::define ((e1 ($smtx_model_eval x1)))
   * (eo::define ((e2 ($smtx_model_eval x2)))
   *  <retTerm>)).
   */
  void addRecReduceSym(const std::string& sym,
                       const std::vector<Kind>& args,
                       Kind ret,
                       const std::string& retTerm);
  /**
   * Add function whose evaluation is
   * ($smtx_model_eval_<sym> ($smtx_model_eval x1) ($smtx_model_eval x2)),
   * where $smtx_model_eval_<sym> is a manually defined program.
   */
  void addHardCodeSym(const std::string& sym, const std::vector<Kind>& args);
  /**
   * Add function whose evaluation is given by
   * ($smtx_model_eval_<sym> ($smtx_model_eval x1) ($smtx_model_eval x2)),
   * where $smtx_model_eval_<sym> is an auto-generated auxiliary
   * program whose case is determined by args, and has <retTerm> as its
   * return, e.g.:
   * (program $smtx_model_eval_<sym>
   *   ((x1 $native_<arg1>) (x2 $native_<arg2>) (t1 $smt_Value) (t2 $smt_Value))
   *   :signature ($smt_Value $smt_Value) $smt_Value
   *   (
   *   (($smtx_model_eval_<sym> ($vsm_<arg1> x1) ($vsm_<arg2> x2)) <retTerm>)
   *   (($smtx_model_eval_<sym> t1 t2) $vsm_not_value)
   *   )
   * )
   * where $vsm_<argi> is the value constructor for the i^th argument kind (see
   * d_kindToEoPrefix) and the trailing default case makes the program total.
   * Note that x1, ..., xn in this context are SMT-LIB literal values.
   */
  void addLitSym(const std::string& sym,
                 const std::vector<Kind>& args,
                 Kind ret,
                 const std::string& retTerm);
  /**
   * Similar to addLitSym, but where <retTerm> is
   * ($vsm_binary_mod_w <retWidth> <retNum>), i.e. the bit-vector value of
   * <retNum> truncated to width <retWidth>.
   *
   * Note reqSameWidth is currently ignored.
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
   * ($vsm_bool ($native_apply_2 "and" x1 x2)).
   * The return kind determines which $vsm_* constructor wraps the return,
   * and the argument kinds determine which literal destructors are used.
   */
  void addConstFoldSym(const std::string& sym,
                       const std::vector<Kind>& args,
                       Kind ret);
  /** Register an SMT-LIB type constructor. */
  void addTypeSym(const std::string& sym, const std::vector<Kind>& args);
  /** Add a hand-written special case for an EO-to-SMT conversion symbol. */
  void addSymCase(const std::string& sym,
                  const std::string& pat,
                  const std::string& ret);
  /**
   * Print a generic generated case to the selected program stream, i.e.
   * ((<mname> (<name> x1 ... xn)) <ret>), where n is nargs. If nargs is zero,
   * name is used as the pattern as-is, which is how a case for a nullary
   * symbol, or one with a pattern of its own, is printed.
   */
  void printEvalCallBase(std::ostream& out,
                         const std::string& mname,
                         const std::string& name,
                         size_t nargs,
                         const std::string& ret);
  /**
   * Helper method for printing the final program case to $smtx_model_eval, i.e.
   * (($smtx_model_eval (<name> x1 ... xn)) <retTerm>).
   */
  void printModelEvalCallBase(const std::string& name,
                              const std::vector<Kind>& args,
                              const std::string& ret);
  /**
   * Helper method for printing a case of the Eunoia to SMT-LIB term layer,
   * i.e. (($eo_to_smt <pat>) <ret>), where pat is a pattern taken verbatim
   * from the reduction file.
   */
  void printEunoiaReduce(const std::string& pat, const std::string& ret);
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
  /** Print embedding declarations and EO-to-SMT conversion cases. */
  void printDecl(const std::string& name,
                 const std::vector<Kind>& args,
                 Kind ret = Kind::PARAM,
                 size_t nopqArgs = 0);
  /** Print one case of an auxiliary evaluator/type program. */
  void printAuxProgramCase(const std::string& name,
                           const std::vector<Kind>& args,
                           const std::string& ret,
                           size_t& paramCount,
                           std::ostream& progCases,
                           std::ostream& progParams,
                           bool isTypeProg = false);
  /** Print an auxiliary evaluator program for literal/value reduction. */
  void printAuxProgram(const std::string& name,
                       const std::vector<Kind>& args,
                       std::stringstream& progCases,
                       std::stringstream& progParams);
  /** Print an auxiliary program that returns an SMT type. */
  void printAuxTypeProgram(const std::string& name,
                           const std::vector<Kind>& args,
                           const std::string& retType,
                           std::stringstream& out);
  /** Register an auxiliary type program for later emission. */
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
  /** Print a `$smtx_typeof` case for an SMT-LIB symbol. */
  void printTypeof(const std::string& name,
                   const std::vector<Kind>& args,
                   Kind ret);

  /** Print a literal/value term of kind k. */
  void printTermInternal(Kind k, const std::string& term, std::ostream& os);
  /** Finalize declaration, main entry point for calling methods above */
  void finalizeDecl(const std::string& name, const Expr& e);
  /** Map from literal kind to `$vsm_*` value constructor prefix. */
  std::map<Kind, std::string> d_kindToEoPrefix;
  /** Map from literal kind to native SMT type name. */
  std::map<Kind, std::string> d_kindToType;
  /** Map from desugared overload names back to SMT-LIB operator names. */
  std::map<std::string, std::string> d_overloadRevert;
  /** Reverse overload map used when matching already-reverted symbols. */
  std::map<std::string, std::string> d_overloadRevertRev;
  /** Number of opaque arguments for selected symbols. */
  std::map<std::string, size_t> d_opqArgs;
  /** Null expression placeholder used by generated expression rewrites. */
  Expr d_null;
  /** Forward declarations for SMT-LIB model-evaluation helper programs. */
  std::stringstream d_modelEvalProgsFwd;
  /** Auxiliary programs for SMT-LIB model evaluation. */
  std::stringstream d_modelEvalProgs;
  /** SMT-LIB model evaluation cases */
  std::stringstream d_eval;
  /** Generated `$eo_to_smt` conversion cases. */
  std::stringstream d_eoToSmt;
  /** Generated `$eo_to_smt_type` conversion cases. */
  std::stringstream d_eoToSmtType;
  /** Auxiliary definitions used by EO-to-SMT conversion. */
  std::stringstream d_eoToSmtAux;
  /** Generated SMT term constructor declarations. */
  std::stringstream d_smtTerms;
  /** Generated SMT type constructor declarations. */
  std::stringstream d_smtTypes;
  /** Generated SMT type rules for terms. */
  std::stringstream d_smtTypeof;
  /** Auxiliary definitions used by SMT type rules. */
  std::stringstream d_smtTypeofAux;
  /** Extra desugar helper definitions required by model_smt. */
  std::stringstream d_desugarAux;
  /** Constant declarations in parser order. */
  std::vector<std::pair<std::string, Expr>> d_declSeen;
  /**
   * The cases of the reduction file whose pattern is not just an application
   * of the symbol to x1 ... xn, mapped from that symbol to the (pattern,
   * return) pairs. They are printed, in the order of the file, before the
   * case of the symbol itself.
   */
  std::map<std::string, std::vector<std::pair<std::string, std::string>>>
      d_specialCases;
  /**
   * Maps a symbol to the auxiliary definitions of the reduction file its
   * reduction requires, by name and in the order of that file. They are
   * emitted at `$EO_TO_SMT_AUX$` when the symbol is declared.
   */
  std::map<std::string, std::vector<std::string>> d_auxDef;
  /** The auxiliary definitions emitted so far, see d_auxDef. */
  std::unordered_set<std::string> d_auxDefEmitted;
  /** Auxiliary definitions substituted at `$SMT_EVAL_PROGS$`. */
  std::map<std::string, std::string> d_auxSmtEval;
  /** Auxiliary definitions of nil terminator recognizers */
  std::map<std::string, std::string> d_auxDesugar;
  /** SMT-LIB types. */
  std::map<std::string, std::vector<Kind>> d_symTypes;
  //--------
  /**
   * Full custom `$eo_to_smt` returns, from the reduction file. A symbol that
   * also has an SMT-LIB semantics of its own, and hence a declaration in the
   * deep embedding, takes its return from here rather than being eliminated,
   * see d_eoSymReduce and finalizeDecl.
   */
  std::map<std::string, std::string> d_eoToSmtFullCase;
  //-------- for defining SMT term type rules
  /** Auxiliary type programs called from `$smtx_typeof`. */
  std::map<std::string, std::string> d_typeCase;
  /** Custom SMT type result for `$smtx_typeof` cases. */
  std::map<std::string, std::string> d_typeRetCase;
  /** Full custom return from `$smtx_typeof`. */
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
  /** Symbols whose reductions evaluate arguments before applying retTerm. */
  std::unordered_set<std::string> d_recReduce;
  /**
   * Eunoia terms that have special reductions to SMT-LIB terms, mapped to the
   * number of arguments of their case and its return.
   */
  std::map<std::string, std::pair<size_t, std::string>> d_eoSymReduce;
  /** Subset of d_eoSymReduce that produce SMT types. */
  std::unordered_set<std::string> d_eoSymReduceTypes;
  /** Symbols that we need no definition for */
  std::map<std::string, bool> d_symIgnore;
  /** SMT-LIB syntax to embedding helper */
  static std::string smtToSmtEmbed(const std::string& str, bool isTerm = false);
  /** Build the embedded return term for a binary bit-vector result. */
  static std::string smtBinaryBinReturn(const std::string& term);
  /** Build an SMT model-evaluation call around s. */
  static std::string smtEval(const std::string& s);
  /** Build an EO let-style define around t before returning ret. */
  static std::string eoDefine(const std::string& x,
                              const std::string& t,
                              const std::string& ret);
  /** Print type internal */
  bool printTypeInternal(const std::string& name, Kind k, std::ostream& out);
  /** Pseudo-kind used for set arguments in generation tables. */
  Kind d_kSet;
  /** Pseudo-kind used for array arguments in generation tables. */
  Kind d_kArray;
  /** Pseudo-kind used for sequence arguments in generation tables. */
  Kind d_kSeq;
  /**
   * Pseudo-kind used for string arguments that are passed to the native
   * layer as unpacked value sequences (List of SmtValue) rather than as
   * native strings. This is used by the regular expression operators, whose
   * native implementations operate directly on value sequences since
   * regular languages carry SmtValue as base elements. Arguments and
   * returns of this kind are typed as String (Seq Char) by the type
   * checker, but are unpacked/packed with unpack_seq/pack_seq.
   */
  Kind d_kStrVSeq;
  /**
   * Pseudo-kind used for regular language arguments in generation tables.
   * Arguments of this kind are typed $smt_RegLan, which is the deep embedding
   * of regular languages (SmtRegLan in both backends; in the SMT2 backend
   * this is an alias of the builtin RegLan sort).
   */
  Kind d_kRegLan;
  /** Pseudo-kind used for bit-vector size arguments in generation tables. */
  Kind d_kBit;
  /** Pseudo-kind used for quoted Int parameters in generation tables. */
  Kind d_kIntQuote;
  /** The Eunoia-to-SMT reduction file, see loadReduceSpec. */
  EoReduceSpec d_reduceSpec;
};

}  // namespace ethos

#endif
