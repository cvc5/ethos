#ifndef STATE_H
#define STATE_H

#include <map>
#include "expr.h"
#include "expr_info.h"
#include "expr_trie.h"

namespace atc {
  
class State
{
public:
  State();
  ~State();
  
  void reset();
  void pushScope();
  void popScope();
  
  /** add assumption */
  void addAssumption(const Expr& a);
  
  /** Type */
  Expr mkType();
  /** (-> <type_list> <type>) */
  Expr mkFunctionType(const std::vector<Expr>& args, const Expr& ret);
  /** ? */
  Expr mkAbstractType();
  /** Bool */
  Expr mkBoolType();
  /** Proof */
  //Expr mkProofType();
  Expr mkProofType(const Expr& proven);
  Expr mkQuoteType(const Expr& t);
  /** */
  Expr mkBuiltinType(Kind k);
  /** */
  Expr mkVar(const std::string& name, const Expr& type);
  /** */
  Expr mkConst(const std::string& name, const Expr& type);
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
private:
  /** */
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
};

}  // namespace atc

#endif /* STATE_H */
