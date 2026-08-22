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
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "../std_plugin.h"

namespace ethos {

/**
 * What the SMT-LIB signature of the deep embedding says about the semantics of
 * one of its symbols, i.e. the content of one of its `$smt_reduce_` defines,
 * see getSmtReduceDefPrefix and ModelSmt::loadSmtSignature.
 */
struct SmtSigReduce
{
  /**
   * The explicit parameters of the define, which are the arguments of the
   * symbol it reduces, in order.
   */
  std::vector<Expr> d_args;
  /** Its body, a term of the SMT-LIB signature. */
  Expr d_body;
};

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
 * A symbol that has no SMT-LIB semantics of its own is instead *eliminated* on
 * the way to the SMT-LIB term layer, by a case of `$eo_to_smt` resp.
 * `$eo_to_smt_type`. Such a reduction comes from one of two places:
 * - A *surface* reduction, i.e. a `define` of the input written in the syntax
 *   of the signature itself, see getReduceDefPrefix and defineReduce. This is
 *   the user-facing way of giving a symbol its semantics. The reductions of a
 *   signature are what makes its reduction file its entry point, so that they
 *   are parsed along with it and carried through the stages before this one;
 *   this plugin only reads them back off its input, in define below.
 * - A reduction registered by addEunoiaReduceSym below, whose right hand side
 *   is a term of the deep embedding. This is for the symbols the input
 *   signature cannot express, e.g. those whose reduction binds a variable,
 *   inspects an SMT-LIB type, or names an operator of the embedding that has
 *   no counterpart in the signature.
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
  /** Capture a surface reduction of the input, see defineReduce. */
  void define(const std::string& name, const Expr& e) override;
  /** Reject a program that is named as though it were a surface reduction. */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Emit the generated EO file containing SMT-LIB model semantics. */
  void finalize() override;

 private:
  /**
   * Parse the SMT-LIB signature of the deep embedding at resourcePath, which
   * declares every symbol that can appear in it under its SMT-LIB name and
   * gives the semantics of some of them as `$smt_reduce_` defines, see
   * getSmtReduceDefPrefix.
   *
   * It declares the SMT-LIB names that the input signature declares as well,
   * so it is parsed in a scope of its own: a name it binds is unbound again
   * before the input is read, and so is never an overload of one of the
   * input's. The symbols arrive through a plugin of its own rather than
   * through the ordinary callbacks of this one, since the signature is not
   * part of the input. What it says is read off into d_smtSigDecl and
   * d_smtSigReduce, whose expressions outlive the scope since they belong to
   * the same state as the rest.
   */
  void loadSmtSignature(const std::string& resourcePath);
  /**
   * Return the kind that classifies the type t of the SMT-LIB signature, e.g.
   * Kind::BOOLEAN for Bool and d_kSeq for (Seq T), or Kind::NONE if it does
   * not classify one. This is the inverse of printTypeInternal: it recovers
   * from a declared type the classification that the generated type rule and
   * the generated constructor are built from, which the registrations below
   * currently state by hand.
   */
  Kind getSmtSigKind(const Expr& t);
  /**
   * Return true if g is the guard by which the SMT-LIB signature says that the
   * type a symbol ranges over is one of the arithmetic types.
   */
  bool isArithGuard(const Expr& g);
  /**
   * Set args and ret to the kinds of the arguments and the result of the
   * symbol named name, as the SMT-LIB signature declares it. Returns false if
   * that signature does not declare it.
   */
  bool getSmtSigKinds(const std::string& name,
                      std::vector<Kind>& args,
                      Kind& ret);
  /** The types the SMT-LIB signature gives its type constructors. */
  std::map<std::string, Expr> d_smtSigTypeCons;
  /**
   * The symbols the SMT-LIB signature declares, mapped to the type it gives
   * them. A type is what says both what the embedding's constructor for the
   * symbol takes and what its case of `$smtx_typeof` computes, so it is what a
   * generated type rule would be derived from.
   */
  std::map<std::string, Expr> d_smtSigDecl;
  /** The reductions the SMT-LIB signature gives, by the symbol they reduce. */
  std::map<std::string, SmtSigReduce> d_smtSigReduce;

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
   * Add function that should be eliminated in the Eunoia to SMT-LIB term
   * layer, where retTerm is a term of the deep embedding, i.e. it is already
   * in the SMT-LIB term layer. It may refer to the arguments of the symbol as
   * x1 ... xn, which are Eunoia terms, so it casts them itself, ordinarily by
   * ($eo_to_smt xi). A reduction that the input signature can express should
   * be a surface reduction instead, see getReduceDefPrefix.
   */
  void addEunoiaReduceSym(const std::string& sym,
                          const std::vector<Kind>& args,
                          const std::string& retTerm,
                          bool isType = false);
  /**
   * Register the surface reduction of sym given by the body of the `define`
   * that carries it, where args are the parameters of that define. Since
   * body is a term of the input signature, its cast into the SMT-LIB term
   * layer is what printSmtEmbed prints, so that e.g. the reduction
   *   (define $eo_reduce_@mod_by_zero ((x Int)) (mod x 0))
   * generates the case
   *   (($eo_to_smt (@mod_by_zero x1))
   *      ($sm_mod ($eo_to_smt x1) ($sm_numeral ($native_apply_0 "0"))))
   * of $eo_to_smt.
   */
  void defineReduce(const std::string& sym,
                    const std::vector<Expr>& args,
                    const Expr& body);
  /**
   * Print the term t of the input signature as the term of the deep embedding
   * it denotes, where args maps each parameter of the reduction of sym to the
   * parameter of the generated case that takes its place. In other words this
   * casts a Eunoia term into the SMT-LIB term layer: an application of a
   * symbol becomes an application of the constructor of the same name, a
   * literal becomes the constructor of its kind applied to its native value,
   * and a parameter, being a Eunoia term at the time the case runs, is cast by
   * $eo_to_smt itself.
   */
  void printSmtEmbed(std::ostream& out,
                     const std::string& sym,
                     const Expr& t,
                     const std::map<Expr, std::string>& args);
  /**
   * If t is a literal, print it as above and return true. Otherwise return
   * false, having printed nothing.
   */
  bool printSmtEmbedLiteral(std::ostream& out, const Expr& t);
  /** Return the native constant whose value is written val. */
  static std::string nativeConst(const std::string& val);
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
  /** Print a generic generated case to the selected program stream. */
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
  /** Special EO-to-SMT cases printed before the matching symbol. */
  std::map<std::string, std::vector<std::pair<std::string, std::string>>>
      d_specialCases;
  /** Auxiliary definitions substituted at `$EO_TO_SMT_AUX$`. */
  std::map<std::string, std::string> d_auxDef;
  /** Auxiliary definitions substituted at `$SMT_EVAL_PROGS$`. */
  std::map<std::string, std::string> d_auxSmtEval;
  /** Auxiliary definitions of nil terminator recognizers */
  std::map<std::string, std::string> d_auxDesugar;
  /** SMT-LIB types. */
  std::map<std::string, std::vector<Kind>> d_symTypes;
  //--------
  /** Full custom `$eo_to_smt` returns for selected SMT-LIB symbols. */
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
   * Eunoia terms that have special reductions to SMT-LIB terms
   */
  std::map<std::string, std::pair<std::vector<Kind>, std::string>>
      d_eoSymReduce;
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
  /**
   * The symbols that are eliminated in the Eunoia to SMT-LIB term layer but
   * that nevertheless name a constructor of the deep embedding, since their
   * reduction is the cast itself. A surface reduction may use these like any
   * symbol with an SMT-LIB semantics, see printSmtEmbed.
   */
  std::unordered_set<std::string> d_smtEmbedBuiltin;
};

}  // namespace ethos

#endif
