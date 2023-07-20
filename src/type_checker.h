#ifndef TYPE_CHECKER_H
#define TYPE_CHECKER_H

#include <map>
#include "expr.h"

namespace atc {

using Ctx = std::map<ExprValue*, ExprValue*>;
/** 
 * Expression class
 */
class TypeChecker
{
 public:
  /** Return its type */
  static Expr getType(Expr& e, std::ostream& out);
 private:
  /** Return its type */
  static Expr getTypeInternal(Expr& e, std::ostream& out);
  static bool match(Expr& a, Expr& b, Ctx& ctx);
  /**
   * Clone this expression, which creates a deep copy of this expression and
   * returns it. The dag structure of pn is the same as that in the returned
   * expression.
   *
   * @return the cloned expression.
   */
  static Expr clone(Expr& e, Ctx& ctx);
};

}  // namespace atc

#endif 
