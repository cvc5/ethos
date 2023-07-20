#ifndef EXPR_H
#define EXPR_H

#include <map>
#include <unordered_set>
#include <vector>
#include <memory>
#include "kind.h"

namespace atc {

class State;
class ExprValue;
class TypeChecker;

/** 
 * Expression class
 */
class ExprValue
{
  friend class State;
  friend class TypeChecker;
 public:
  ExprValue();
  ExprValue(Kind k,
       const std::vector<std::shared_ptr<ExprValue>>& children);
  ~ExprValue();
  /** is null? */
  bool isNull() const;
  /** is equal */
  bool isEqual(const std::shared_ptr<ExprValue>& val) const;
  /** get the kind of this expression */
  Kind getKind() const;
  /** Get children */
  const std::vector<std::shared_ptr<ExprValue>>& getChildren() const;
  /** Get num children */
  size_t getNumChildren() const;  
  /**
   * Returns the i-th child of this node.
   * @param i the index of the child
   * @return the node representing the i-th child
   */
  std::shared_ptr<ExprValue> operator[](size_t i) const;
  /** Print debug on output strem os
   *
   * @param os the stream to print to
   */
  static void printDebug(const std::shared_ptr<ExprValue>& e, std::ostream& os);

  /** Get the free symbols */
  std::unordered_set<std::shared_ptr<ExprValue>> getFreeSymbols() const;
  /** Has variable */
  bool hasVariable();
 private:
  /** The current state */
  static State* d_state;
  /** The kind */
  Kind d_kind;
  /** The children of this expression */
  std::vector<std::shared_ptr<ExprValue>> d_children;
  /** Its type */
  std::shared_ptr<ExprValue> d_type;
  /** flags */
  enum class Flag
  {
    HAS_VARIABLE = (1 << 0),
    HAS_VARIABLE_COMPUTED = (1 << 1)
  };
  char d_flags;
  /** Get flag */
  bool getFlag(Flag f) const
  {
    return static_cast<uint8_t>(d_flags) & static_cast<uint8_t>(f);
  }
  /** Set flag */
  void setFlag(Flag f, bool value)
  {
    if (value)
    {
      d_flags |= static_cast<uint8_t>(f);
    }
    else
    {
      d_flags &= static_cast<uint8_t>(f);
    }
  }
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
