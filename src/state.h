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

class State;

/**
 * Reads the commands of a file into a state. The state is independent of any
 * concrete syntax: when a file is included, it resolves the path, performs its
 * bookkeeping, and then delegates reading the file to this interface. The
 * standard implementation is ParserFileReader in parser/parser.h.
 */
class FileReader
{
 public:
  virtual ~FileReader() {}
  /**
   * Read all commands of the file at path into s.
   * @param s The state to populate.
   * @param path The (canonical) path of the file.
   * @param isSignature Whether the file is a signature file.
   * @param isReference Whether the file is a reference file.
   */
  virtual void readFile(State& s,
                        const Filepath& path,
                        bool isSignature,
                        bool isReference) = 0;
};

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
  /** Require the last proof step at level zero to prove false. */
  bool d_requireProofOfFalse;
  bool d_normalizeDecimal;
  bool d_normalizeHexadecimal;
  /** Treat numerals as rational literals */
  bool d_normalizeNumeral;
  /**
   * In reference files, parse SMT-LIB define-fun and define-const commands as
   * Eunoia-style definitions instead of translating them to reference assertions.
   */
  bool d_referenceDefineFun;
};

/**
 * The state class which manages the symbol table, the expression database, and
 * proof checking. It does not depend on the parser; files are read via a
 * FileReader, see setFileReader.
 */
class State
{
  friend class TypeChecker;
  friend class ExprValue;
  // the parser's term builder uses the internal methods for constructing terms
  friend class TermBuilder;

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
  /**
   * Include file, if not already done, return false if error. Requires a file
   * reader to have been set, unless the plugin handles the include.
   */
  bool includeFile(const std::string& s, bool isSignature);
  /** include file, possibly as a reference */
  bool includeFile(const std::string& s, bool isSignature, bool isReference, const Expr& referenceNf);
  /** add assumption */
  bool addAssumption(const Expr& a);
  /** add reference assert */
  void addReferenceAssert(const Expr& a);
  /**
   * Discard all reference assertions, as e.g. done by the smt2 command
   * reset-assertions.
   */
  void clearReferenceAsserts();
  /**
   * Set type rule for literal kind k to t, returns false if the type rule for
   * k was already set to a different type.
   */
  bool setLiteralTypeRule(Kind k, const Expr& t, std::ostream* out = nullptr);
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
  /** Define, called when a define command is parsed.
   * @param name The name of the define.
   * @param e The expression name is defined to be.
   */
  void define(const std::string& name, const Expr& e);
  /** Echo, called when an echo command is parsed.
   * @param msg The message of the echo command.
   */
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
  Expr mkSymbol(Kind k, const std::string& name, const Expr& type);
  /** (eo::requires <pair>+ <type>) */
  Expr mkRequires(const std::vector<Expr>& args, const Expr& ret);
  /** (eo::requires <arg1> <arg2> <type>) */
  Expr mkRequires(const Expr& a1, const Expr& a2, const Expr& ret);
  /** */
  Expr mkSelf() const;
  /** Make pair */
  Expr mkPair(const Expr& t1, const Expr& t2);
  /**
   * Makes expression with given kind and childen. Applications are curried,
   * applications of lambdas are beta-reduced and applications of programs and
   * literal operators are evaluated eagerly where possible. N-ary literal
   * operators are left-associated, e.g. (eo::add t1 t2 t3) is
   * (eo::add (eo::add t1 t2) t3).
   *
   * Note this method does not apply the desugaring based on the attributes of
   * the operator head (e.g. :right-assoc-nil) or the syntax of builtin
   * operators (e.g. ->, _, eo::as), nor does it resolve overloading. This is
   * done in the parser, see TermBuilder in parser/term_builder.h.
   */
  Expr mkExpr(Kind k, const std::vector<Expr>& children);
  /** Same as above, without evaluation */
  Expr mkRawExpr(Kind k, const std::vector<Expr>& children);
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
   * Make (eo::List::cons a1 (eo::List::cons a2 ... eo::List::nil)) for args
   * a1 ... an. Returns eo::List::nil if args is empty.
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
  /**
   * Get the constructor kind for symbol v. This is one of the types listed in
   * attr.h which impact how the symbol v is parsed on interpreted.
   */
  Attr getAttributeKind(const ExprValue* v) const;
  /**
   * Get the attribute term for symbol v. Along with getAttributeKind, this
   * term impacts how the symbol v is parsed on interpreted.
   */
  Expr getAttributeTerm(const ExprValue* v) const;
  /**
   * Get the variable with the given name or nullptr if it does not exist. If
   * name is bound to multiple terms, this returns the most recent one.
   */
  Expr getVar(const std::string& name) const;
  /**
   * Get all terms the given name is bound to in the current scope, in the
   * order they were bound, or nullptr if the name is not bound. Names bound
   * to more than one term are interpreted as overloaded by the parser. The
   * returned pointer is valid until the next call to bind or popScope.
   */
  const std::vector<Expr>* getBindings(const std::string& name) const;
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
   * account whether the rule was marked :conclusion-explicit or :assumption
   * (for step-pop commands), or whether the plugin can provide the result.
   * If the rule was marked :premise-list, the caller is responsible for
   * combining the premises into a single premise beforehand.
   * Note that result may be a term that is not of type Bool. This check is
   * instead done in the parser.
   * @param name The name of the step.
   * @param rule The proof rule being applied.
   * @param proven The conclusion of the proof rule, if provided.
   * @param premises The premises of the proof rule, after combining them for
   * rules marked :premise-list.
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
  /** Did the last checked step prove false at assumption level zero? */
  bool lastStepProvesFalseAtLevelZero() const;
  /** Get the program */
  Expr getProgram(const ExprValue* ev);
  /** */
  size_t getAssumptionLevel() const;
  /**
   * Get the name of the most recently opened assumption scope, which requires
   * getAssumptionLevel() > 0.
   */
  std::string getOpenAssumptionName() const;
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
  /** Set the file reader, used by includeFile */
  void setFileReader(FileReader* r);

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
  /** Make (<APPLY> children), curried. */
  ExprValue* mkApplyInternal(const std::vector<ExprValue*>& children);
  /**
   * Beta-reduce the application of a lambda, children[0], to the remaining
   * children. Returns the null expression if the number of arguments does
   * not match the number of variables of the lambda.
   */
  Expr mkBetaReduceInternal(const std::vector<ExprValue*>& children);
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
  /** Get the internal data for expression e. */
  AppInfo* getAppInfo(const ExprValue* e);
  const AppInfo* getAppInfo(const ExprValue* e) const;
  /** Bind builtin */
  void bindBuiltin(const std::string& name, Kind k, Attr ac = Attr::NONE);
  /** Bind builtin */
  void bindBuiltin(const std::string& name, Kind k, Attr ac, const Expr& t);
  /** Bind builtin eval */
  void bindBuiltinEval(const std::string& name, Kind k, Attr ac = Attr::NONE);
  //--------------------- parsing state
  /**
   * The symbol table, mapping symbols to the terms they are bound to, where
   * the last one is the current binding. Symbols bound to multiple terms are
   * either shadowed or overloaded; the parser makes this distinction.
   */
  std::map<std::string, std::vector<Expr>> d_symTable;
  /** Symbol table for proof rules, if using separate table */
  std::map<std::string, Expr> d_ruleSymTable;
  /**
   * The list of declared symbols in the order they were bound.
   */
  std::vector<std::string> d_decls;
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
  /** Whether the last checked step proved false at assumption level zero. */
  bool d_lastStepProvesFalseAtLevelZero;
  //--------------------- utilities
  /** Options */
  Options& d_opts;
  /** Stats */
  Stats& d_stats;
  /** Type checker */
  TypeChecker d_tc;
  /** Plugin, if using one */
  Plugin* d_plugin;
  /** The file reader, if set */
  FileReader* d_fileReader;
};

}  // namespace ethos

#endif /* STATE_H */
