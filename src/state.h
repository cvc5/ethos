#ifndef STATE_H
#define STATE_H

#include <map>
#include <set>
#include <string>

#include "expr.h"
#include "expr_info.h"
#include "expr_trie.h"
#include "type_checker.h"

namespace alfc {
  
class State
{
public:
  State();
  ~State();
  /** Reset */
  void reset();
  /** Push scope */
  void pushScope();
  /** Pop scope */
  void popScope();
  /** include file, if not already done */
  void includeFile(const std::string& s);
  /** add assumption */
  void addAssumption(const Expr& a);
  /** Type */
  Expr mkType();
  /** (-> <type>+ <type>) */
  Expr mkFunctionType(const std::vector<Expr>& args, const Expr& ret);
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
  Expr mkVar(const std::string& name, const Expr& type);
  /** */
  Expr mkConst(const std::string& name, const Expr& type);
  /** */
  Expr mkProgramConst(const std::string& name, const Expr& type);
  /** */
  Expr mkExpr(Kind k, const std::vector<Expr>& children);
  
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
  ExprInfo* getInfo(const ExprValue* e);
  /** */
  ExprInfo* getOrMkInfo(const ExprValue* e);
  /** Get the type checker */
  TypeChecker& getTypeChecker();
  
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog);
  /** Has program? */
  bool hasProgram(const Expr& v) const;
  /** Maybe evaluate */
  Expr evaluate(const std::vector<Expr>& children, Ctx& newCtx);
private:
  /** */
  Expr mkSymbolInternal(Kind k, const std::string& name, const Expr& type);
  Expr mkExprInternal(Kind k, const std::vector<Expr>& children, bool doHash=true);
  /** 
   * Bind builtin
   */
  void bindBuiltin(const std::string& name, Kind k, bool isClosure);
  /** 
   * Bind builtin
   */
  void bindBuiltin(const std::string& name, Kind k, bool isClosure, const Expr& t);
  /** All free assumptions */
  std::vector<Expr> d_assumptions;
  /** The symbol table */
  std::map<std::string, Expr> d_symTable;
  /** Context stacks */
  std::vector<std::string> d_decls;
  /** Context size */
  std::vector<size_t> d_declsSizeCtx;
  /** literals */
  std::map<const ExprValue*, ExprInfo> d_exprData;
  /** hash */
  std::map<Kind, ExprTrie> d_trie;
  /** hash for literals */
  std::map< std::pair<Kind, std::string>, Expr> d_literalTrie;
  /** files included */
  std::set<std::string> d_includes;
  /** Programs */
  std::map<Expr, Expr> d_programs;
  /** Type checker */
  TypeChecker d_tc;
};

}  // namespace alfc

#endif /* STATE_H */
