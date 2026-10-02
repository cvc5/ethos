/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef TERM_BUILDER_H
#define TERM_BUILDER_H

#include <ostream>
#include <vector>

#include "expr.h"
#include "expr_info.h"
#include "state.h"

namespace ethos {

/**
 * Constructs the terms that are written in the surface syntax. This class
 * implements the desugaring of applications based on the attributes of their
 * head (e.g. :right-assoc-nil, :chainable, :opaque), the syntax of builtin
 * operators (e.g. ->, _, as, eo::as), overload resolution, binder lists, and
 * premise lists. The terms it constructs are then built by the State, which
 * is independent of this syntax.
 *
 * This class has no state of its own. In particular, the overloads of a symbol
 * are the terms its name is bound to, see State::getBindings.
 */
class TermBuilder
{
 public:
  /**
   * The overloads of the children of a term we are constructing. If
   * non-empty, the i^th element is the candidate terms for the i^th child, or
   * nullptr if that child is not an overloaded symbol. This vector may be
   * shorter than the children, in which case the remaining children are not
   * overloaded symbols.
   */
  using Overloads = std::vector<const std::vector<Expr>*>;
  TermBuilder(State& s);
  /**
   * Makes expression with given kind and childen, which applies the
   * desugaring described above.
   * @param k The kind of the expression.
   * @param children The children, which for applications includes the head.
   * @param overloads The overloads of the children, see Overloads.
   */
  Expr mkExpr(Kind k,
              const std::vector<Expr>& children,
              const Overloads& overloads = {});
  /**
   * Make binder list for a binder ev, e.g. a symbol marked :binder whose
   * constructor term is the list constructor for its variable list vs.
   */
  Expr mkBinderList(const ExprValue* ev, const std::vector<Expr>& vs);
  /**
   * Make the let binder list for a symbol ev marked :let-binder, where lls are
   * the pairs of variables and terms they are bound to.
   */
  Expr mkLetBinderList(const ExprValue* ev,
                       const std::vector<std::pair<Expr, Expr>>& lls);
  /**
   * Make the premise of a step for a proof rule marked :premise-list. This
   * combines the provided premises (pf F1) ... (pf Fn) into a single premise
   * (pf (f F1 ... Fn)), where f is the given premise list constructor. If n is
   * zero, this is (pf nil) where nil is the nil terminator of f.
   * @param plCons The premise list constructor f.
   * @param premises The provided premises.
   * @param err If provided, details on errors are printed to this stream.
   * @return The premise, or the null term if the premises are not proofs, or
   * if the premise list constructor has no nil terminator when n is zero.
   */
  Expr mkPremiseList(const Expr& plCons,
                     const std::vector<Expr>& premises,
                     std::ostream* err = nullptr);

 private:
  /**
   * Make (<APPLY> children) based on attribute. Returns the null term if the
   * attribute does not impact how to build the application.
   * @param ai The attribute of the head.
   * @param vchildren The children, including the head term.
   * @param consTerm The computed constructor term correspond to the
   * application.
   * @return The application of vchildren based on ai, or the null term if
   * the default construction should be used to construct the application.
   */
  Expr mkApplyAttr(AppInfo* ai,
                   const std::vector<ExprValue*>& vchildren,
                   const Expr& consTerm);
  /**
   * Get overload internal. This determines which one of the operators
   * in overloads (if any) should be applied in the Kind::APPLY we are
   * constructing with the given children.
   * @param overloads The candidate operators.
   * @param children The children of the Kind::APPLY we are trying to
   * construct. This includes a head operator.
   * @param retType If non-null, this is required return type of the
   * application.
   * @param retApply If true, we return the application of the
   * appropriate overloaded constructor to children; otherwise we return the
   * overloaded constructor itself.
   * @return If possible, one of the elements of overloads that meets
   * the above requirements. If multiple are possible, we return the
   * first only. If none are possible, we return the null expression.
   */
  Expr getOverloadInternal(const std::vector<Expr>& overloads,
                           const std::vector<Expr>& children,
                           const ExprValue* retType = nullptr,
                           bool retApply = false);
  /** The state */
  State& d_state;
  /** The type checker */
  TypeChecker& d_tc;
  /** The null expression */
  Expr d_null;
};

}  // namespace ethos

#endif /* TERM_BUILDER_H */
