/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef EXPR_H
#define EXPR_H

#include <cstdint>
#include <map>
#include <unordered_set>
#include <vector>
#include <memory>
#include "kind.h"

namespace ethos {

class State;
class ExprValue;
class TypeChecker;
class Expr;
class Literal;

/** 
 * Expression class
 */
class ExprValue
{
  friend class TypeChecker;
  friend class Expr;
  friend class State;

 public:
  ExprValue();
  ExprValue(Kind k, const std::vector<ExprValue*>& children);
  ~ExprValue();
  /** as literal */
  virtual const Literal* asLiteral() const { return nullptr; }
  /** is null? */
  bool isNull() const;
  /** get the kind of this expression */
  Kind getKind() const;
  /** Get children */
  const std::vector<ExprValue*>& getChildren() const;
  /** Get num children */
  size_t getNumChildren() const;  
  /**
   * Returns the i-th child of this node.
   * @param i the index of the child
   * @return the node representing the i-th child
   */
  ExprValue* operator[](size_t i) const;
  /** Has variable */
  bool isEvaluatable();
  /** Has variable */
  bool isGround();
 protected:
  /** The kind */
  Kind d_kind;
  /** The children of this expression */
  std::vector<ExprValue*> d_children;
  /**
   * Flags, indicating properties of the term.
   */
  enum class Flag
  {
    NONE = 0,
    /** Have we computed the flags for this term? */
    IS_FLAGS_COMPUTED = (1 << 0),
    /**
     * Is the term "evaluatable", i.e. contains a literal op, program or oracle
     * as a subterm?
     */
    IS_EVAL = (1 << 1),
    /**
     * Is the term non-ground, i.e. contains a parameter as a subterm?
     */
    IS_NON_GROUND = (1 << 2),
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
  void inc(){ d_rc++; }
  void dec();
  /** Null */
  static ExprValue s_null;
  /** The current state */
  static State* d_state;
};

class Expr
{
 public:
  explicit Expr();
  explicit Expr(const ExprValue* ev);
  Expr(const Expr& e);
  ~Expr();
  /** Get the free parameters in expression e */
  static std::vector<Expr> getVariables(const Expr& e);
  /** Get the free parameters in vector es */
  static std::vector<Expr> getVariables(const std::vector<Expr>& es);
  /** Get the free symbols */
  static bool hasVariable(const Expr& e,
                          const std::unordered_set<const ExprValue*>& terms);
  /**
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
  /** Set this expression equal to e */
  Expr& operator=(const Expr& e);
  /** Returns true if this expression is equal to e*/
  bool operator==(const Expr& e) const;
  /** Returns true if this expression is not equal to e*/
  bool operator!=(const Expr& e) const;
  /** */
  bool operator<(const Expr& e) const;
  /** is null */
  bool isNull() const;
  /** get the kind of this expression */
  Kind getKind() const;
  /** Has variable */
  bool isEvaluatable() const;
  /** Has variable */
  bool isGround() const;
  /** Get symbol */
  std::string getSymbol() const;
  /** Get underlying value */
  ExprValue* getValue() const;
  /**
   * Get function type, which is a pair of argument types and the range type.
   */
  std::pair<std::vector<Expr>, Expr> getFunctionType() const;
  /** Get arity, where this is a function type. Used for overloading. */
  size_t getFunctionArity() const;
  /** */
  static std::map<const ExprValue*, size_t> computeLetBinding(
      const Expr& e, std::vector<Expr>& ll);

 private:
  /** The underlying value */
  ExprValue* d_value;
  /** */
  static void printDebugInternal(const Expr& e,
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
std::ostream& operator<<(std::ostream& out, const std::vector<ExprValue*>& es);

using Ctx = std::map<ExprValue*, ExprValue*>;
std::ostream& operator<<(std::ostream& out, const Ctx& c);

}  // namespace ethos

#endif 
