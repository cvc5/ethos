#ifndef EXPR_H
#define EXPR_H

#include <map>
#include <unordered_set>
#include <vector>
#include <memory>
#include "kind.h"

namespace alfc {

class Compiler;
class State;
class ExprValue;
class TypeChecker;
class Expr;

/** 
 * Expression class
 */
class ExprValue
{
  friend class Compiler;
  friend class State;
  friend class TypeChecker;
  friend class Expr;
 public:
  ExprValue();
  ExprValue(Kind k,
       const std::vector<ExprValue*>& children);
  ~ExprValue();
  /** is null? */
  bool isNull() const;
  /** get the kind of this expression */
  Kind getKind() const;
  /** Get children */
  std::vector<ExprValue*>& getChildren();
  /** Get num children */
  size_t getNumChildren() const;  
  /**
   * Returns the i-th child of this node.
   * @param i the index of the child
   * @return the node representing the i-th child
   */
  ExprValue* operator[](size_t i) const;
 private:
  /** The current state */
  static State* d_state;
  /** The kind */
  Kind d_kind;
  /** The children of this expression */
  std::vector<ExprValue*> d_children;
  /** flags */
  enum class Flag
  {
    NONE = 0,
    IS_FLAGS_COMPUTED = (1 << 0),
    IS_EVAL = (1 << 1),
    IS_PROG_EVAL = (1 << 2),
    IS_NON_GROUND = (1 << 3),
    IS_COMPILED = (1 << 4)
  };
  char d_flags;
  /** */
  uint32_t d_rc;
  /** Compute flags */
  void computeFlags();
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
      d_flags &= ~static_cast<uint8_t>(f);
    }
  }
  /** reference counting */
  void inc();
  void dec();
  /** Null */
  static ExprValue s_null;
};
using Expr = Expr;


class Expr
{
  friend class State;
public:
  Expr();
  Expr(const ExprValue* ev);
  ~Expr();
  /** Get the free symbols */
  static std::vector<Expr> getVariables(const Expr& e);
  static std::vector<Expr> getVariables(const std::vector<Expr>& es);
  /** Get the free symbols */
  static bool hasVariable(const Expr& e,
                          const std::unordered_set<Expr>& terms);
  /** Print debug on output strem os
   *
   * @param os the stream to print to
   */
  static void printDebug(const Expr& e, std::ostream& os);
  /** Get num children */
  size_t getNumChildren() const;
  /**
   * Returns the i-th child of this node.
   * @param i the index of the child
   * @return the node representing the i-th child
   */
  Expr operator[](size_t i) const;
  /**
   */
  Expr operator=(const Expr& e) const;
  bool operator==(const Expr& e) const;
  bool operator!=(const Expr& e) const;
  /** is null */
  bool isNull() const;
  /** get the kind of this expression */
  Kind getKind() const;
  /** Has variable */
  bool isEvaluatable();
  /** Has variable */
  bool isGround();
  /** Has program variable */
  bool isProgEvaluatable();
  /** Is part of compiled code */
  bool isCompiled();
  /** Get symbol */
  std::string getSymbol() const;
private:
  ExprValue* d_value;
  /** Its type */
  ExprValue* d_type;
  /** */
  static std::map<const ExprValue*, size_t> computeLetBinding(
                                const Expr& e,
                                std::vector<const ExprValue*>& ll);
  static void printDebugInternal(const ExprValue* e,
                                 std::ostream& os,
                                 std::map<const ExprValue*, size_t>& lbind);
};

/**
 * Serializes a given expression to the given stream.
 *
 * @param out the output stream to use
 * @param e the expression to output to the stream
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const Expr& e);

}  // namespace alfc

#endif 
