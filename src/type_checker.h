#ifndef TYPE_CHECKER_H
#define TYPE_CHECKER_H

#include <map>
#include <set>
#include "expr.h"

namespace alfc {

class State;

using Ctx = std::map<Expr, Expr>;
std::ostream& operator<<(std::ostream& out, const Ctx& c);
/** 
 * Expression class
 */
class TypeChecker
{
 public:
  TypeChecker(State& s);
  ~TypeChecker();
  /** Return its type */
  Expr getType(Expr& e, std::ostream* out = nullptr);
  /** Set type rule for literal */
  void setTypeRule(Kind k, const Expr& t);
  /** */
  bool match(Expr& a, Expr& b, Ctx& ctx, std::set<std::pair<Expr, Expr>>& visited);
  bool match(Expr& a, Expr& b, Ctx& ctx);
  /**
   * Clone this expression, which creates a deep copy of this expression and
   * returns it. The dag structure of pn is the same as that in the returned
   * expression.
   *
   * @return the cloned expression.
   */
  Expr evaluate(Expr& e, Ctx& ctx);
  Expr evaluate(Expr& e);
  /** Get the free symbols */
  std::vector<Expr> getFreeSymbols(Expr& e) const;
 private:
  /** Compiled version */
  Expr run_getTypeInternal(Expr& hd, std::vector<Expr>& args, std::ostream* out);
  /** Return its type */
  Expr getTypeInternal(Expr& e, std::ostream* out);
  /** Compiled version */
  Expr run_evaluate(Expr& hd, std::vector<Expr>& args);
  /** The state */
  State& d_state;
  /** The builtin literal kinds */
  std::set<Kind> d_literalKinds;
  /** Mapping literal kinds to type rules */
  std::map<Kind, Expr> d_literalTypeRules;
};

}  // namespace alfc

#endif 
