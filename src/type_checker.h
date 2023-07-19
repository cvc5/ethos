#ifndef TYPE_CHECKER_H
#define TYPE_CHECKER_H

#include "expr.h"

namespace atc {

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
};

}  // namespace atc

#endif 
