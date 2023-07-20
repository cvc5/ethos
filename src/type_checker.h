#ifndef TYPE_CHECKER_H
#define TYPE_CHECKER_H

#include <map>
#include "expr.h"

namespace atc {

class State;

using Ctx = std::map<Expr, Expr>;
/** 
 * Expression class
 */
class TypeChecker
{
 public:
  TypeChecker(State& s);
  ~TypeChecker();
  /** Return its type */
  Expr getType(Expr& e, std::ostream& out);
 private:
  /** Return its type */
  Expr getTypeInternal(Expr& e, std::ostream& out);
  bool match(Expr& a, Expr& b, Ctx& ctx);
  /**
   * Clone this expression, which creates a deep copy of this expression and
   * returns it. The dag structure of pn is the same as that in the returned
   * expression.
   *
   * @return the cloned expression.
   */
  Expr clone(Expr& e, Ctx& ctx);
  /** The state */
  State& d_state;
};

}  // namespace atc

#endif 
