#ifndef STATE_H
#define STATE_H

#include "expr.h"

namespace atc {

class State
{
public:
  State();
  ~State();
  
  void reset();
  void pushScope();
  void popScope();
  
  /** */
  Expr mkType();
  /** */
  Expr mkFunctionType(const std::vector<Expr>& args, const Expr& ret);
  /** */
  Expr mkVar(const std::string& s, const Expr& type);
  /** */
  Expr mkExpr(Kind k, const std::vector<Expr>& children);
  
  /**
   * Create an integer constant from a string.
   * @param s The string representation of the constant, may represent an
   *          integer (e.g., "123").
   * @return A constant of sort Integer assuming 's' represents an integer)
   */
  Expr mkLiteral(Kind k, const std::string& s) const;
  
  /**
   * Create a new cvc5 bound variable expressions of the given names and types.
   * Like the method above, this binds these names to those variables in the
   * current scope.
   */
  std::vector<Expr> bindBoundVars(
      std::vector<std::pair<std::string, Expr> >& sortedVarNames);
private:
  
};

}  // namespace atc

#endif /* STATE_H */
