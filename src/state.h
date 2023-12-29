#ifndef STATE_H
#define STATE_H

#include <map>
#include <set>
#include <string>
#include <unordered_map>

#include "attr.h"
#include "compiler.h"
#include "expr.h"
#include "expr_info.h"
#include "expr_trie.h"
#include "literal.h"
#include "stats.h"
#include "type_checker.h"
#include "util/filesystem.h"

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
  bool d_normalizeDecimal;
  bool d_normalizeHexadecimal;
};

/**
 * The state class which manages both the parsing state and the expression database.
 */
class State
{
  friend class TypeChecker;
  friend class Compiler;
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
  bool includeFile(const std::string& s);
  /** include file, possibly as a reference */
  bool includeFile(const std::string& s, bool isReference, const Expr& referenceNf);
  /** add assumption */
  bool addAssumption(const Expr& a);
  /** add reference assert */
  void addReferenceAssert(const Expr& a);
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t);
  /** */
  bool bind(const std::string& name, const Expr& e);
  /** Mark constructor kind */
  bool markConstructorKind(const Expr& v, Attr a, const Expr& cons);
  /** Define program, where v is PROGRAM_CONST and prog is PROGRAM. */
  void defineProgram(const Expr& v, const Expr& prog);
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
  Expr mkSymbol(Kind k, const std::string& name, const Expr& type);
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
  bool isClosure(const ExprValue* ev) const;
  /** Get the variable with the given name or nullptr if it does not exist */
  Expr getVar(const std::string& name) const;
  /** Get the proof rule with the given name or nullptr if it does not exist */
  Expr getProofRule(const std::string& name) const;
  /** Returns true if e is a rule that matches on the conclusion */
  bool matchesConclusion(const ExprValue* rule);
  /** Get actual premises */
  bool getActualPremises(const ExprValue* ev,
                         std::vector<Expr>& given,
                         std::vector<Expr>& actual);
  /** Get the program */
  Expr getProgram(const ExprValue* ev);
  /** Get the oracle command */
  bool getOracleCmd(const ExprValue* ev, std::string& ocmd);
  /** */
  size_t getAssumptionLevel() const;
  /** */
  std::vector<Expr> getCurrentAssumptions() const;
  /** Get hash for expression */
  size_t getHash(const ExprValue* ev);
  /** Has reference */
  bool hasReference() const;
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
  Expr d_null;
  Expr d_type;
  Expr d_boolType;
  Expr d_absType;
  Expr d_true;
  Expr d_false;
  Expr d_self;
  Expr d_nil;
  Expr d_fail;
  /** Get the constructor kind for symbol v */
  Attr getConstructorKind(const ExprValue* v) const;
  /** Mark that file s was included */
  bool markIncluded(const Filepath& s);
  /** mark deleted */
  void markDeleted(ExprValue* e);
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
  /** Get the internal data for expression e. */
  AppInfo* getAppInfo(const ExprValue* e);
  /** lookup type */
  ExprValue* lookupType(const ExprValue* e) const;
  /** Bind builtin */
  void bindBuiltin(const std::string& name, Kind k, Attr ac = Attr::NONE);
  /** Bind builtin */
  void bindBuiltin(const std::string& name, Kind k, Attr ac, const Expr& t);
  /** Bind builtin eval */
  void bindBuiltinEval(const std::string& name, Kind k, Attr ac = Attr::NONE);
  /** Compiled initialization code. */
  void run_initialize();
  //--------------------- parsing state
  /** The symbol table */
  std::map<std::string, Expr> d_symTable;
  /** Symbol table for proof rules, if using separate table */
  std::map<std::string, Expr> d_ruleSymTable;
  /** Context stacks */
  std::vector<std::pair<std::string, size_t>> d_decls;
  /** Context size */
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
