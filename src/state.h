#ifndef STATE_H
#define STATE_H

#include <map>
#include "expr.h"
#include "expr_info.h"

namespace atc {
  
class State
{
public:
  State();
  ~State();
  
  void reset();
  void pushScope();
  void popScope();
  
  /** Type */
  Expr mkType();
  /** (-> <type_list> <type>) */
  Expr mkFunctionType(const std::vector<Expr>& args, const Expr& ret);
  /** ? */
  Expr mkAbstractType();
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
  
  /**
   * Create a new cvc5 bound variable expressions of the given names and types.
   * Like the method above, this binds these names to those variables in the
   * current scope.
   */
  bool mkAndBindVars(
      const std::vector<std::pair<std::string, Expr> >& sortedVarNames, std::vector<Expr>& ret);
  /** */
  bool bind(const std::string& name, const Expr& e);
  /** is closure */
  bool isClosure(const Expr& e) const;
  /** */
  Expr getVar(const std::string& name) const;
  /** */
  ExprInfo* getInfo(const Expr& e);
  /** */
  ExprInfo* getOrMkInfo(const Expr& e);
private:
  /** 
   * Bind builtin
   */
  void bindBuiltin(const std::string& name, Kind k, bool isClosure);
  /** The symbol table */
  std::map<std::string, Expr> d_symTable;
  // TODO: reverse lookup for names?
  /** Context stacks */
  std::vector<std::string> d_decls;
  /** Context size */
  std::vector<size_t> d_declsSizeCtx;
  /** literals */
  std::map<Expr, ExprInfo> d_exprData;
};

}  // namespace atc

#endif /* STATE_H */
