#ifndef STATE_H
#define STATE_H

#include <map>
#include <set>
#include <string>
#include <filesystem>

#include "attr.h"
#include "stats.h"
#include "expr.h"
#include "expr_info.h"
#include "expr_trie.h"
#include "type_checker.h"
#include "compiler.h"
#include "literal.h"

namespace alfc {

class Options
{
public:
  Options();
  bool d_compile;
  bool d_runCompile;
  bool d_printLet;
  bool d_stats;
  bool d_ruleSymTable;
};

class State
{
  friend class TypeChecker;
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
  /** include file, if not already done */
  void includeFile(const std::string& s, bool isReference = false);
  /** add assumption */
  bool addAssumption(const Expr& a);
  /** add reference assert */
  void addReferenceAssert(const Expr& a);
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t);
  /** */
  bool bind(const std::string& name, const Expr& e);
  /** Mark constructor kind */
  void markConstructorKind(const Expr& v, Attr a, const Expr& cons);
  /** Define program, where v is PROGRAM_CONST and prog is PROGRAM. */
  void defineProgram(const Expr& v, const Expr& prog);
  /** Mark has reference */
  void markHasReference();
  //--------------------------------------
  /** Type */
  Expr mkType();
  /** Make type constant (-> Type ... Type Type) */
  Expr mkTypeConstant(const std::string& name, size_t arity);
  /** (-> <type>+ <type>) */
  Expr mkFunctionType(const std::vector<Expr>& args, const Expr& ret, bool flatten = true);
  /** ? */
  Expr mkAbstractType();
  /** Bool */
  Expr mkBoolType();
  /** (Proof <proven>) */
  Expr mkProofType(const Expr& proven);
  /** (Quote <term>) */
  Expr mkQuoteType(const Expr& t);
  /** */
  Expr mkBuiltinType(Kind k);
  /** */
  Expr mkAnnotatedType(const Expr& t, Attr ck, const Expr& cons);
  /** */
  Expr mkParameter(const std::string& name, const Expr& type);
  /** */
  Expr mkVar(const std::string& name, const Expr& type);
  /** */
  Expr mkConst(const std::string& name, const Expr& type);
  /** */
  Expr mkProgramConst(const std::string& name, const Expr& type);
  /** */
  Expr mkProofRule(const std::string& name, const Expr& type);
  /** */
  Expr mkOracle(const std::string& name, const Expr& type);
  /** (alf.requires <pair>+ <type>) */
  Expr mkRequires(const std::vector<Expr>& args, const Expr& ret);
  /** (alf.requires <arg1> <arg2> <type>) */
  Expr mkRequires(const Expr& a1, const Expr& a2, const Expr& ret);
  /** alf.nil */
  Expr mkNil();
  /** */
  Expr mkSelf();
  /** Make pair */
  Expr mkPair(const Expr& t1, const Expr& t2);
  /** */
  Expr mkExpr(Kind k, const std::vector<Expr>& children);
  /** make true */
  Expr mkTrue();
  /** make false */
  Expr mkFalse();
  /**
   * Create a literal from a string.
   * @param s The string representation of the literal, may represent an
   *          integer (e.g., "123").
   * @return A constant
   */
  Expr mkLiteral(Kind k, const std::string& s);
  //--------------------------------------
  /** is closure */
  bool isClosure(const Expr& e) const;
  /** */
  Expr getVar(const std::string& name) const;
  /** */
  Expr getProofRule(const std::string& name) const;
  /** */
  Literal* getLiteral(const ExprValue* e);
  /** Get actual premises */
  bool getActualPremises(const Expr& rule, std::vector<Expr>& given, std::vector<Expr>& actual);
  /** Get the oracle command */
  bool getOracleCmd(const Expr& oracle, std::string& ocmd);
  /** */
  size_t getAssumptionLevel() const;
  /** */
  std::vector<Expr> getCurrentAssumptions() const;
  /** Print compiled files (for --show-config) */
  static std::string showCompiledFiles();
  //--------------------------------------
  /** Get the type checker */
  TypeChecker& getTypeChecker();
  /** Get options */
  Options& getOptions();
  /** Get stats */
  Stats& getStats();
  /** Get compiler */
  Compiler* getCompiler();
private:
  /** Common constants */
  Expr d_type;
  Expr d_boolType;
  Expr d_true;
  Expr d_false;
  Expr d_self;
  Expr d_nil;
  Expr d_fail;
  /** Have we parsed a reference file to check assumptions */
  bool d_hasReference;
  /** Get the constructor kind for symbol v */
  Attr getConstructorKind(const ExprValue* v) const;
  /** mark included */
  bool markIncluded(const std::string& s);
  /** */
  Expr mkApplyInternal(const std::vector<Expr>& children);
  Expr mkExprInternal(Kind k, const std::vector<Expr>& children);
  /** */
  Expr mkSymbolInternal(Kind k, const std::string& name, const Expr& type);
  /** */
  AppInfo* getAppInfo(const ExprValue* e);
  /** Bind builtin */
  void bindBuiltin(const std::string& name, Kind k, bool isClosure = false);
  /** Bind builtin */
  void bindBuiltin(const std::string& name, Kind k, bool isClosure, const Expr& t);
  /** Bind builtin eval */
  void bindBuiltinEval(const std::string& name, Kind k);
  /** Compiled initialization */
  void run_initialize();
  //--------------------- parsing state
  /** The symbol table */
  std::map<std::string, Expr> d_symTable;
  /** Symbol table for proof rules */
  std::map<std::string, Expr> d_ruleSymTable;
  /** Context stacks */
  std::vector<std::string> d_decls;
  /** Context size */
  std::vector<size_t> d_declsSizeCtx;
  /** All free assumptions */
  std::vector<Expr> d_assumptions;
  /** Context size */
  std::vector<size_t> d_assumptionsSizeCtx;
  /** Reference asserts */
  std::unordered_set<Expr> d_referenceAsserts;
  //--------------------- expression info
  /** literals */
  std::map<const ExprValue*, AppInfo> d_appData;
  /** hash */
  std::map<Kind, ExprTrie> d_trie;
  /** oracle */
  std::map<const ExprValue*, std::string> d_oracleCmd;
  //--------------------- literals
  /** hash for literals */
  std::map<std::pair<Kind, std::string>, Expr> d_literalTrie;
  /** literal data */
  std::map<const ExprValue*, Literal> d_literals;
  // -------------------- symbols
  std::map<std::tuple<Kind, std::string, Expr>, Expr> d_symcMap;
  //--------------------- includes
  /** input file */
  std::filesystem::path d_inputFile;
  /** files included */
  std::set<std::filesystem::path> d_includes;
  //--------------------- utilities
  /** Type checker */
  TypeChecker d_tc;
  /** Options */
  Options& d_opts;
  /** Stats */
  Stats& d_stats;
  /** Compiler, if compiling code */
  std::unique_ptr<Compiler> d_compiler;
};

}  // namespace alfc

#endif /* STATE_H */
