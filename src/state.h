#ifndef STATE_H
#define STATE_H

#include <map>
#include <set>
#include <string>
#include <filesystem>

#include "attr.h"
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
};

class Stats
{
public:
  Stats();
  size_t d_mkExprCount;
  size_t d_exprCount;
  size_t d_symCount;
  size_t d_litCount;
  std::string toString();
};

class State
{
  friend class TypeChecker;
public:
  State(Options& opts, Stats& stats);
  ~State();
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
  void includeFile(const std::string& s);
  /** add assumption */
  void addAssumption(const Expr& a);
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t);
  /** Type */
  Expr mkType();
  /** Make type constant (-> Type ... Type Type) */
  Expr mkTypeConstant(const std::string& name, size_t arity);
  /** (-> <type>+ <type>) */
  Expr mkFunctionType(const std::vector<Expr>& args, const Expr& ret, bool flatten = true);
  /** (requires <pair>+ <type>) */
  Expr mkRequiresType(const std::vector<Expr>& args, const Expr& ret);
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
  Expr mkParameter(const std::string& name, const Expr& type);
  /** */
  Expr mkVar(const std::string& name, const Expr& type);
  /** */
  Expr mkConst(const std::string& name, const Expr& type);
  /** */
  Expr mkProgramConst(const std::string& name, const Expr& type);
  /** */
  Expr mkProofRule(const std::string& name, const Expr& type);
  /** (nil <type>) */
  Expr mkNil(const Expr& t);
  /** */
  Expr mkSelf();
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
  /** */
  bool bind(const std::string& name, const Expr& e);
  /** is closure */
  bool isClosure(const Expr& e) const;
  
  /** */
  Expr getVar(const std::string& name) const;
  /** */
  Literal* getLiteral(const ExprValue* e);
  /** Get the type checker */
  TypeChecker& getTypeChecker();
  /** Get options */
  Options& getOptions();
  /** Get compiler */
  Compiler* getCompiler();
  /** */
  size_t getAssumptionLevel() const;
  /** */
  std::vector<Expr> getCurrentAssumptions() const;
  
  /** Mark information */
  bool markAttributes(const Expr& v, const AttrMap& attrs);
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog);
  /** Define constructor */
  void defineConstructor(const Expr& c, const std::vector<Expr>& sels);
  /** Define datatype */
  void defineDatatype(const Expr& d, const std::vector<Expr>& cons);
private:
  /** Common constants */
  Expr d_type;
  Expr d_boolType;
  Expr d_true;
  Expr d_false;
  Expr d_self;
  /** include file, if not already done */
  void includeFileInternal(const std::string& s, bool ignore=false);
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
  /** Context stacks */
  std::vector<std::string> d_decls;
  /** Context size */
  std::vector<size_t> d_declsSizeCtx;
  /** All free assumptions */
  std::vector<Expr> d_assumptions;
  /** Context size */
  std::vector<size_t> d_assumptionsSizeCtx;
  //--------------------- expression info
  /** literals */
  std::map<const ExprValue*, AppInfo> d_appData;
  /** hash */
  std::map<Kind, ExprTrie> d_trie;
  //--------------------- literals
  /** hash for literals */
  std::map<std::pair<Kind, std::string>, Expr> d_literalTrie;
  /** literal data */
  std::map<const ExprValue*, Literal> d_literals;
  //--------------------- datatypes
  /** datatypes */
  std::map<const ExprValue*, std::vector<Expr>> d_dts;
  /** constructors */
  std::map<const ExprValue*, std::vector<Expr>> d_dtcons;
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
