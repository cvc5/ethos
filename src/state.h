/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef STATE_H
#define STATE_H

#include <map>
#include <set>
#include <string>
#include <unordered_map>

#include "attr.h"
#include "plugin.h"
#include "expr.h"
#include "expr_info.h"
#include "expr_trie.h"
#include "literal.h"
#include "stats.h"
#include "type_checker.h"
#include "util/filesystem.h"

namespace ethos {

class Options
{
 public:
  Options();
  /**
   * @return true if the option was successfully set.
   */
  bool setOption(const std::string& key, bool val);
  bool d_printDag;
  /** 'let' is lexed as the SMT-LIB syntax for a dag term specified by a let */
  bool d_parseLet;
  bool d_stats;
  bool d_statsAll;
  bool d_statsCompact;
  bool d_ruleSymTable;
  bool d_normalizeDecimal;
  bool d_normalizeHexadecimal;
  /** Treat numerals as rational literals */
  bool d_normalizeNumeral;
  /** plugins */
  bool d_pluginDesugar;
  bool d_pluginDesugarGenVc;
  bool d_pluginSmtMeta;
  bool d_pluginSmtMetaSygus;
  bool d_pluginLeanMeta;
  bool d_pluginTrimDefs;
  bool d_pluginModelSmt;
  bool d_pluginModelSmtNew;
};

/**
 * The state class which manages both the parsing state and the expression database.
 */
class State
{
  friend class TypeChecker;
  friend class ExprValue;

 public:
  State(Options& opts, Stats& stats);
  ~State();
  //--------------------------------------
  /** Reset */
  void reset();
  /** Push scope */
  void pushScope();
  /** Pop scope */
  void popScope();
  /** Push assumption scope */
  void pushAssumptionScope();
  /** Pop assumption scope */
  void popAssumptionScope();
  /** include file, if not already done, return false if error */
  bool includeFile(const std::string& s, bool isSignature);
  /** include file, possibly as a reference */
  bool includeFile(const std::string& s, bool isSignature, bool isReference, const Expr& referenceNf);
  /** add assumption */
  bool addAssumption(const Expr& a);
  /** add reference assert */
  void addReferenceAssert(const Expr& a);
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t);
  /** */
  bool bind(const std::string& name, const Expr& e);
  /** 
   * Mark constructor kind.
   * @param v The function symbol we are marking.
   * @param a The constructor kind we are marking v with.
   * @param cons The constructor associated with v, e.g. the nil terminator
   * if a is right associative with nil.
   */
  bool markConstructorKind(const Expr& v, Attr a, const Expr& cons);
  /** Define program, where v is PROGRAM_CONST and prog is PROGRAM. */
  void defineProgram(const Expr& v, const Expr& prog);
  /** Define */
  void define(const std::string& name, const Expr& e);
  /** Echo */
  void echo(const std::string& msg);
  //--------------------------------------
  /** Type */
  Expr mkType();
  /** Make type constant (-> Type ... Type Type) */
  Expr mkTypeConstant(const std::string& name, size_t arity);
  /** (-> <type>+ <type>) */
  Expr mkFunctionType(const std::vector<Expr>& args, const Expr& ret);
  /** (-> <type>+ <type>) */
  Expr mkProgramType(const std::vector<Expr>& args, const Expr& ret);
  /** Bool */
  Expr mkBoolType();
  /** eo::List */
  Expr mkListType();
  /** eo::List::cons */
  Expr mkListCons();
  /** eo::List::nil */
  Expr mkListNil();
  /** The Proof type, which is an ordinary simple type */
  Expr mkProofType();
  /** (pf <proven>), where <proven> is a formula. */
  Expr mkProof(const Expr& proven);
  /** (Quote <term>) */
  Expr mkQuoteType(const Expr& t);
  /** */
  Expr mkBuiltinType(Kind k);
  /** */
  Expr mkSymbol(Kind k, const std::string& name, const Expr& type);
  /** (eo::requires <pair>+ <type>) */
  Expr mkRequires(const std::vector<Expr>& args, const Expr& ret);
  /** (eo::requires <arg1> <arg2> <type>) */
  Expr mkRequires(const Expr& a1, const Expr& a2, const Expr& ret);
  /** */
  Expr mkSelf() const;
  /** Make pair */
  Expr mkPair(const Expr& t1, const Expr& t2);
  /** */
  Expr mkExpr(Kind k, const std::vector<Expr>& children);
  /** Same as above, without desugaring */
  Expr mkExprSimple(Kind k, const std::vector<Expr>& children);
  /** make true */
  Expr mkTrue() const;
  /** make false */
  Expr mkFalse() const;
  /** make Boolean value */
  Expr mkBool(bool val) const;
  /** Make any */
  Expr mkAny() const;
  /**
   * Create a literal from a string.
   * @param s The string representation of the literal, may represent an
   *          integer (e.g., "123").
   * @return A constant
   */
  Expr mkLiteral(Kind k, const std::string& s);
  /**
   * Make parameterized with given parameters
   */
  Expr mkParameterized(const ExprValue* hd, const std::vector<Expr>& params);
  /**
   * Make (eo::List::Cons <args>) if args is non-empty or eo::List::nil
   * otherwise.
   */
  Expr mkList(const std::vector<Expr>& args);
  /**
   * Make disambiguated type. This constructs the type of a symbol which we
   * expect to be written as (as <symbol> <type>), which is parsed as an
   * opaque application of that symbol to that type as its first argument. This
   * method returns a type of the form (-> (Quote x) ($eo_disamb_type_<name> x))
   * where $eo_disamb_type_<name> is a program defined by this method, and x
   * has type Type.
   *
   * @param disambPat The pattern which is expected as the second argument to
   *                  "as" above.
   * @param ret The return type, whose free parameters are a subset of the free
   *            parameters of disambPat. This is typically either disambPat,
   *            or a function type whose return type is disambPat.
   * @param name The name of the symbol we are disambiguating.
   */
  Expr mkDisambiguatedType(const Expr& disambPat,
                           const Expr& ret,
                           const std::string& name);
  //--------------------------------------
  /** Get the constructor kind for symbol v */
  Attr getConstructorKind(const ExprValue* v) const;
  /** make binder list */
  Expr mkBinderList(const ExprValue* ev, const std::vector<Expr>& vs);
  /** */
  Expr mkLetBinderList(const ExprValue* ev, const std::vector<std::pair<Expr, Expr>>& lls);
  /** Get the variable with the given name or nullptr if it does not exist */
  Expr getVar(const std::string& name) const;
  /**
   * Get the bound variable with the given type. This method always returns the
   * same variable for the same name and type.
   */
  Expr getBoundVar(const std::string& name, const Expr& type);
  /** Get the proof rule with the given name or nullptr if it does not exist */
  Expr getProofRule(const std::string& name) const;
  /**
   * Notify assume, called when an assume command is parsed.
   * @param name The name of the assumption.
   * @param proven The formula that it assumes.
   * @param isPush true iff the assumption was from an assume-push command.
   */
  void notifyAssume(const std::string& name, Expr& proven, bool isPush);
  /**
   * Notify step, called when a step command is parsed.
   * This method determines the argument list to a proof rule in a step or
   * step-pop and computes the result of what the step proves. This takes into
   * account whether the rule was marked :premise-list, :conclusion-explicit,
   * or :assumption (for step-pop commands), or whether the plugin can provide
   * the result.
   * Note that result may be a term that is not of type Bool. This check is
   * instead done in the parser.
   * @param name The name of the step.
   * @param rule The proof rule being applied.
   * @param proven The conclusion of the proof rule, if provided.
   * @param premises The provided premises of the proof rule.
   * @param args The provided arguments of the proof rule.
   * @param isPop Whether we were a step-pop.
   * @param result The result proven by the step.
   * @param err If provided, details on errors are printed to this stream.
   * @return true if we successfully computed result. Otherwise, a proof
   * checking error should be thrown.
   */
  bool notifyStep(const std::string& name,
                  Expr& rule,
                  Expr& proven,
                  std::vector<Expr>& premises,
                  std::vector<Expr>& args,
                  bool isPop,
                  Expr& result,
                  std::ostream* err = nullptr);
  /** Get the program */
  Expr getProgram(const ExprValue* ev);
  /** */
  size_t getAssumptionLevel() const;
  /** */
  std::vector<Expr> getCurrentAssumptions() const;
  /** Get hash for expression */
  size_t getHash(const ExprValue* ev);
  /**
   * Lookup type, returns the type of e if it has been computed, or nullptr
   * otherwise.
   *
   * @param e The term whose type we want to lookup.
   * @return the type of e if it has been computed already.
   */
  ExprValue* lookupType(const ExprValue* e) const;
  /** Have we already run a reference command? */
  bool hasReference() const;
  /** Mark e as a proof rule with :sorry */
  void markProofRuleSorry(const ExprValue * e);
  /** Does e refer to a proof rule marked :sorry? */
  bool isProofRuleSorry(const ExprValue* e) const;
  //--------------------------------------
  /** Get the type checker */
  TypeChecker& getTypeChecker();
  /** Get options */
  Options& getOptions();
  /** Get stats */
  Stats& getStats();
  /** Set the plugin */
  void setPlugin(Plugin* p);
  /** Get plugin */
  Plugin* getPlugin();

  /** Get the internal data for expression e. */
  AppInfo* getAppInfo(const ExprValue* e);

 private:
  /** Common constants */
  Expr d_null;
  Expr d_type;
  Expr d_boolType;
  Expr d_true;
  Expr d_false;
  Expr d_self;
  Expr d_any;
  Expr d_fail;
  Expr d_listType;
  Expr d_listNil;
  Expr d_listCons;
  /** The proof type */
  Expr d_proofType;
  /** Mark that file s was included */
  bool markIncluded(const Filepath& s);
  /** mark deleted */
  void markDeleted(ExprValue* e);
  /**
   * Make (<APPLY> children) based on attribute. Returns the null term if the
   * attribute does not impact how to build the application.
   * @param ai The attribute of the head.
   * @param vchildren The children, including the head term.
   * @param consTerm The computed constructor term correspond to the
   * application.
   * @return The application of vchildren based on ai, or the null term if
   * the default construction should be used to construct the application.
   */
  Expr mkApplyAttr(AppInfo* ai,
                   const std::vector<ExprValue*>& vchildren,
                   const Expr& consTerm);
  /** Make (<APPLY> children), curried. */
  ExprValue* mkApplyInternal(const std::vector<ExprValue*>& children);
  /**
   * Constructs a new expression from k and children, or returns a
   * previous one if the same call to mkExprInternal was made previously.
   */
  ExprValue* mkExprInternal(Kind k, const std::vector<ExprValue*>& children);
  /** Constructs a symbol-like expression with the given kind, name and type. */
  ExprValue* mkSymbolInternal(Kind k,
                              const std::string& name,
                              const Expr& type);
  /** Make literal internal */
  ExprValue* mkLiteralInternal(Literal& l);
  /**
   * Get overload internal. This determines which one of the operators
   * in overloads (if any) should be applied in the Kind::APPLY we are
   * constructing with the given children.
   * @param overloads The candidate operators.
   * @param children The children of the Kind::APPLY we are trying to
   * construct. This includes a head operator.
   * @param retType If non-null, this is required return type of the
   * application.
   * @param retApply If true, we return the application of the
   * appropriate overloaded constructor to children; otherwise we return the
   * overloaded constructor itself.
   * @return If possible, one of the elements of overloads that meets
   * the above requirements. If multiple are possible, we return the
   * first only. If none are possible, we return the null expression.
   */
  Expr getOverloadInternal(const std::vector<Expr>& overloads,
                           const std::vector<Expr>& children,
                           const ExprValue* retType = nullptr,
                           bool retApply = false);
  const AppInfo* getAppInfo(const ExprValue* e) const;
  /** Bind builtin */
  void bindBuiltin(const std::string& name, Kind k, Attr ac = Attr::NONE);
  /** Bind builtin */
  void bindBuiltin(const std::string& name, Kind k, Attr ac, const Expr& t);
  /** Bind builtin eval */
  void bindBuiltinEval(const std::string& name, Kind k, Attr ac = Attr::NONE);
  //--------------------- parsing state
  /** The symbol table, mapping symbols */
  std::map<std::string, Expr> d_symTable;
  /** Symbol table for proof rules, if using separate table */
  std::map<std::string, Expr> d_ruleSymTable;
  /** The (canonical) bound variables for binders */
  std::map<std::pair<std::string, const ExprValue*>, Expr> d_boundVars;
  /**
   * The list of declared symbols in the order they were bound.
   */
  std::vector<std::string> d_decls;
  /**
   * The list of declared symbols that were overloaded when they
   * were bound. This is a sublist of d_decls. For example if
   *   d_decls = { "A", "B", "A", "C", "A", "B" }
   * then
   *   d_overloadedDecls = { "A", "A", "B" }.
   */
  std::vector<std::string> d_overloadedDecls;
  /**
   * Maps symbols that are bound to >= 2 terms to the list of all terms bound
   * to that symbol. Each vector in the range of this map has size >=2.
   */
  std::map<std::string, std::vector<Expr>> d_overloads;
  /**
   * Context size, which is the size of d_decls at the time of when each
   * current pushScope was called.
   */
  std::vector<size_t> d_declsSizeCtx;
  /** All free assumptions */
  std::vector<Expr> d_assumptions;
  /** Context size */
  std::vector<size_t> d_assumptionsSizeCtx;
  //--------------------- expression info
  /** Map from expressions to constructor info */
  std::map<const ExprValue*, AppInfo> d_appData;
  /** Map from expressions to hash */
  std::map<const ExprValue*, size_t> d_hashMap;
  /** Mapping expressions to types */
  std::map<const ExprValue*, Expr> d_typeCache;
  /** Hash counter */
  size_t d_hashCounter;
  /** The database of created expressions */
  std::map<Kind, ExprTrie> d_trie;
  //--------------------- literals
  /** Cache for literals */
  std::unordered_map<Rational, Expr, RationalHashFunction> d_litRatMap[2];
  std::unordered_map<String, Expr, StringHashFunction> d_litStrMap;
  std::unordered_map<Integer, Expr, IntegerHashFunction> d_litIntMap;
  std::unordered_map<BitVector, Expr, BitVectorHashFunction> d_litBvMap[2];
  // -------------------- symbols
  /** Cache for symbols */
  // std::map<std::tuple<Kind, std::string, const ExprValue *>, Expr> d_symcMap;
  //--------------------- includes
  /** input file */
  Filepath d_inputFile;
  /** The proof rules marked :sorry */
  std::unordered_set<const ExprValue*> d_pfrSorry;
  /** Cache of files included */
  std::set<Filepath> d_includes;
  /** Have we parsed a reference file to check assumptions? */
  bool d_hasReference;
  /** The reference normalization function, if it exists */
  Expr d_referenceNf;
  /** Reference asserts */
  std::unordered_set<const ExprValue*> d_referenceAsserts;
  /** Reference assert list */
  std::vector<Expr> d_referenceAssertList;
  //--------------------- garbage collection
  /** The current set of expression values to delete */
  std::vector<ExprValue*> d_toDelete;
  /** Are we in garbage collection? */
  bool d_inGarbageCollection;
  //--------------------- utilities
  /** Options */
  Options& d_opts;
  /** Stats */
  Stats& d_stats;
  /** Type checker */
  TypeChecker d_tc;
  /** Plugin, if using one */
  Plugin* d_plugin;
};

}  // namespace ethos

#endif /* STATE_H */
