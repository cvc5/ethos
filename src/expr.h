#ifndef EXPR_H
#define EXPR_H

#include <vector>
#include <memory>
#include "kind.h"

namespace atc {

/** 
 * Expression class
 */
class ExprValue
{
 public:
  ExprValue();
  ExprValue(Kind k,
       const std::vector<std::shared_ptr<ExprValue>>& children);
  ~ExprValue();
  bool isNull() const;
  /** get the kind of this expression */
  Kind getKind() const;
  /** Get children */
  const std::vector<std::shared_ptr<ExprValue>>& getChildren() const;
  /**
   * Clone this expression, which creates a deep copy of this expression and
   * returns it. The dag structure of pn is the same as that in the returned
   * expression.
   *
   * @return the cloned expression.
   */
  //std::shared_ptr<Expr> clone() const;
  /** Print debug on output strem os
   *
   * @param os the stream to print to
   */
  void printDebug(std::ostream& os) const;

  /** Its type */
  std::shared_ptr<ExprValue> getType();
 private:
  /** The kind */
  Kind d_kind;
  /** The children of this expression */
  std::vector<std::shared_ptr<ExprValue>> d_children;
};
using Expr = std::shared_ptr<ExprValue>;

/**
 * Serializes a given expression to the given stream.
 *
 * @param out the output stream to use
 * @param e the expression to output to the stream
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const Expr& e);

}  // namespace atc

#endif 
