/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "expr_builder.h"

#include "base/check.h"
#include "base/output.h"
#include "state.h"

namespace ethos {
namespace expr_builder {

Expr mkApply(State& state, const std::vector<Expr>& children)
{
  Assert(!children.empty());
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  ExprValue* hd = vchildren[0];
  AppInfo* ai = state.getAppInfo(hd);
  if (ai != nullptr)
  {
    // Compute the "constructor term" for the operator, which may involve
    // type inference. We store the constructor term in consTerm and operator
    // in hdTerm, where notice hdTerm is of kind PARAMETERIZED if consTerm
    // (prior to resolution) was PARAMETERIZED. So, for example, applying
    // `bvor` to `a` of type `(BitVec 4)` results in
    //   consTerm := #b0000.
    Expr consTerm = state.computeConstructorTerm(ai, children);
    Expr ret = mkApplyAttr(state, ai, vchildren, consTerm);
    if (!ret.isNull())
    {
      return ret;
    }
  }
  Kind hk = hd->getKind();
  if (hk == Kind::LAMBDA)
  {
    // beta-reduce eagerly, if the correct arity
    const std::vector<ExprValue*>& vars = (*hd)[0]->getChildren();
    size_t nvars = vars.size();
    if (nvars == children.size() - 1)
    {
      Ctx ctx;
      for (size_t i = 0; i < nvars; i++)
      {
        ctx[vars[i]] = vchildren[i + 1];
      }
      Expr ret = state.d_tc.evaluate((*hd)[1], ctx);
      Trace("state") << "BETA_REDUCE " << Expr((*hd)[1]) << " " << ctx
                     << " = " << ret << std::endl;
      return ret;
    }
    Warning() << "Wrong number of arguments when applying " << Expr(hd)
              << std::endl;
  }
  else if (hk == Kind::PROGRAM_CONST)
  {
    // have to check whether we have marked the constructor kind, which is
    // not the case i.e. if we are constructing applications corresponding to
    // the cases in the program definition itself.
    if (state.getConstructorKind(hd) != Attr::NONE)
    {
      Expr hdt = Expr(hd);
      const Expr& t = state.d_tc.getType(hdt);
      // only do this if the correct arity
      if (t.getNumChildren() == children.size())
      {
        Ctx ctx;
        Expr e = state.evaluateProgramInternal(vchildren, ctx);
        if (!e.isNull())
        {
          Expr ret = state.d_tc.evaluate(e.getValue(), ctx);
          Trace("state") << "EAGER_EVALUATE " << ret << std::endl;
          return ret;
        }
      }
      else
      {
        Warning() << "Wrong number of arguments when applying program "
                  << Expr(hd) << ", " << t.getNumChildren()
                  << " arguments expected, got " << children.size()
                  << std::endl;
      }
    }
  }
  // Most functions are unary and require currying if applied to more than one
  // argument. The exceptions to this are operators whose types are not
  // flattened (programs and proof rules).
  if (children.size() > 2 && hk != Kind::PROGRAM_CONST
      && hk != Kind::PROOF_RULE)
  {
    return Expr(state.mkApplyInternal(vchildren));
  }
  return Expr(state.mkExprInternal(Kind::APPLY, vchildren));
}

Expr mkApplyAttr(State& state,
                 AppInfo* ai,
                 const std::vector<ExprValue*>& vchildren,
                 const Expr& consTerm)
{
  ExprValue* hd = vchildren[0];
  Trace("state-debug") << "Process category " << ai->d_attrCons << " for "
                       << Expr(vchildren[0]) << std::endl;
  size_t nchild = vchildren.size();
  Trace("state-debug") << "...updated " << consTerm << std::endl;
  // if it has a constructor attribute
  switch (ai->d_attrCons)
  {
    case Attr::LEFT_ASSOC:
    case Attr::RIGHT_ASSOC:
    case Attr::LEFT_ASSOC_NIL:
    case Attr::RIGHT_ASSOC_NIL:
    case Attr::RIGHT_ASSOC_NS_NIL:
    case Attr::LEFT_ASSOC_NS_NIL:
    {
      // This means that we don't construct bogus terms when e.g.
      // right-assoc-nil operators are used in side condition bodies.
      // note that nchild>=2 treats e.g. (or a) as (or a false).
      // checking nchild>2 treats (or a) as a function Bool -> Bool.
      if (nchild >= 2)
      {
        bool isLeft = (ai->d_attrCons == Attr::LEFT_ASSOC
                       || ai->d_attrCons == Attr::LEFT_ASSOC_NIL
                       || ai->d_attrCons == Attr::LEFT_ASSOC_NS_NIL);
        bool isNsNil = (ai->d_attrCons == Attr::RIGHT_ASSOC_NS_NIL
                        || ai->d_attrCons == Attr::LEFT_ASSOC_NS_NIL);
        bool isNil = (isNsNil || ai->d_attrCons == Attr::RIGHT_ASSOC_NIL
                      || ai->d_attrCons == Attr::LEFT_ASSOC_NIL);
        size_t i = 1;
        ExprValue* curr = vchildren[isLeft ? i : nchild - i];
        std::vector<ExprValue*> cc{hd, nullptr, nullptr};
        size_t nextIndex = isLeft ? 2 : 1;
        size_t prevIndex = isLeft ? 1 : 2;
        size_t nlistTerms = 0;
        if (isNil)
        {
          if (state.getConstructorKind(curr) != Attr::LIST)
          {
            // if the last term is not marked as a list variable and
            // we have a null terminator, then we insert the null terminator
            Trace("state-debug")
                << "...insert nil terminator " << consTerm << std::endl;
            if (consTerm.isNull())
            {
              // if we failed to infer a nil terminator (likely due to
              // a non-ground parameter), then we insert a placeholder
              // (eo::nil f (eo::typeof t1)), which if t1 is non-ground
              // will evaluate to the proper nil terminator when
              // instantiated.
              Expr typ =
                  Expr(state.mkExprInternal(Kind::EVAL_TYPE_OF, {vchildren[1]}));
              curr = state.mkExprInternal(Kind::EVAL_NIL,
                                          {vchildren[0], typ.getValue()});
            }
            else
            {
              curr = consTerm.getValue();
            }
            i--;
          }
        }
        // now, add the remaining children
        i++;
        while (i < nchild)
        {
          cc[prevIndex] = curr;
          cc[nextIndex] = vchildren[isLeft ? i : nchild - i];
          // if the "head" child is marked as list, we construct concatenation
          if (isNil && state.getConstructorKind(cc[nextIndex]) == Attr::LIST)
          {
            curr = state.mkExprInternal(Kind::EVAL_LIST_CONCAT, cc);
          }
          else
          {
            nlistTerms++;
            curr = state.mkApplyInternal(cc);
          }
          i++;
        }
        // if we are a non-singleton list with fewer than 2 non-list children
        if (isNsNil && nlistTerms < 2)
        {
          // If we are a "non-singleton" kind, we add singleton elimination.
          // Note that this case is applied possibly on ground arguments,
          // in contrast to the case of EVAL_LIST_CONCAT above which requires a
          // :list annotation, which can only be applied to parameters. Hence,
          // we must call mkExpr in case we evaluate this application
          // immediately.
          std::vector<Expr> ccse;
          ccse.emplace_back(hd);
          ccse.emplace_back(curr);
          return state.mkLiteralOp(Kind::EVAL_LIST_SINGLETON_ELIM, ccse);
        }
        Trace("type_checker")
            << "...return for " << Expr(vchildren[0]) << std::endl;
        return Expr(curr);
      }
      // Otherwise we are applying the operator to zero arguments. This
      // can never occur in standard parsing since it is not possible
      // to apply a function to zero arguments. However, this case may
      // arise if e.g. a pairwise or chainable operator is applied to
      // exactly one argument, e.g. (distinct t) is equivalent to true.
      return consTerm;
    }
    break;
    case Attr::CHAINABLE:
    {
      std::vector<Expr> cchildren;
      Assert(!consTerm.isNull());
      cchildren.push_back(consTerm);
      std::vector<ExprValue*> cc{hd, nullptr, nullptr};
      for (size_t i = 1, nchild = vchildren.size() - 1; i < nchild; i++)
      {
        cc[1] = vchildren[i];
        cc[2] = vchildren[i + 1];
        cchildren.emplace_back(state.mkApplyInternal(cc));
      }
      if (cchildren.size() == 2)
      {
        // no need to chain
        return cchildren[1];
      }
      // note this could loop
      return mkApply(state, cchildren);
    }
    break;
    case Attr::PAIRWISE:
    {
      std::vector<Expr> cchildren;
      Assert(!consTerm.isNull());
      cchildren.push_back(consTerm);
      std::vector<ExprValue*> cc{hd, nullptr, nullptr};
      for (size_t i = 1, nchild = vchildren.size(); i < nchild - 1; i++)
      {
        for (size_t j = i + 1; j < nchild; j++)
        {
          cc[1] = vchildren[i];
          cc[2] = vchildren[j];
          cchildren.emplace_back(state.mkApplyInternal(cc));
        }
      }
      if (cchildren.size() == 2)
      {
        // no need to chain
        return cchildren[1];
      }
      // note this could loop
      return mkApply(state, cchildren);
    }
    break;
    case Attr::ARG_LIST:
    {
      Expr argList;
      // If there is only one argument, and it was marked :list, then it is
      // not desugared.
      if (vchildren.size() == 2
          && state.getConstructorKind(vchildren[1]) == Attr::LIST)
      {
        argList = Expr(vchildren[1]);
      }
      else
      {
        std::vector<Expr> cchildren;
        Assert(!consTerm.isNull());
        cchildren.push_back(consTerm);
        for (size_t i = 1, nchild = vchildren.size(); i < nchild; i++)
        {
          cchildren.emplace_back(vchildren[i]);
        }
        argList = mkApply(state, cchildren);
      }
      return Expr(
          state.mkExprInternal(Kind::APPLY, {vchildren[0], argList.getValue()}));
    }
    break;
    case Attr::OPAQUE:
    {
      // determine how many opaque children
      Expr hdt = Expr(hd);
      const Expr& t = state.d_tc.getType(hdt);
      Assert(t.getKind() == Kind::FUNCTION_TYPE);
      // get the number of opaque arguments, stored as the constructor term
      Expr acons = ai->d_attrConsTerm;
      Assert(acons.getKind() == Kind::NUMERAL);
      Assert(acons.getValue()->asLiteral()->d_int.fitsUnsignedInt());
      size_t nargs = acons.getValue()->asLiteral()->d_int.toUnsignedInt();
      if (nargs >= vchildren.size())
      {
        Warning() << "Too few arguments when applying opaque symbol " << hdt
                  << std::endl;
      }
      else
      {
        // construct curried APPLY_OPAQUE application.
        ExprValue* curr = vchildren[0];
        for (size_t i = 1; i < nargs + 1; i++)
        {
          curr = state.mkExprInternal(Kind::APPLY_OPAQUE, {curr, vchildren[i]});
        }
        Expr op = Expr(curr);
        Trace("opaque") << "Construct opaque operator " << op << std::endl;
        if (nargs + 1 == vchildren.size())
        {
          Trace("opaque") << "...return operator" << std::endl;
          return op;
        }
        // higher order
        std::vector<ExprValue*> rchildren;
        rchildren.push_back(op.getValue());
        rchildren.insert(
            rchildren.end(), vchildren.begin() + 1 + nargs, vchildren.end());
        Trace("opaque") << "...return operator applied to children"
                        << std::endl;
        if (rchildren.size() > 2)
        {
          return Expr(state.mkApplyInternal(rchildren));
        }
        return Expr(state.mkExprInternal(Kind::APPLY, rchildren));
      }
    }
    default: break;
  }
  return Expr();
}

Expr mkExpr(State& state, Kind k, const std::vector<Expr>& children)
{
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  if (k == Kind::APPLY)
  {
    Assert(!children.empty());
    ExprValue* hd = vchildren[0];
    AppInfo* ai = state.getAppInfo(hd);
    if (ai != nullptr)
    {
      if (ai->d_kind != Kind::NONE)
      {
        Trace("state-debug") << "Process builtin app " << ai->d_kind
                             << std::endl;
        if (ai->d_kind == Kind::FUNCTION_TYPE)
        {
          // Functions (from parsing) are flattened here.
          std::vector<Expr> achildren(children.begin() + 1, children.end() - 1);
          return state.mkFunctionType(achildren, children.back());
        }
        if (ai->d_kind == Kind::APPLY)
        {
          // Applications (_ f ...) do *not* recursively desugar.
          // Remove the dummy operator "_".
          vchildren.erase(vchildren.begin(), vchildren.begin() + 1);
          return Expr(vchildren.size() > 2
                          ? state.mkApplyInternal(vchildren)
                          : state.mkExprInternal(Kind::APPLY, vchildren));
        }
        // Another builtin operator, possibly APPLY.
        std::vector<Expr> achildren(children.begin() + 1, children.end());
        return mkExpr(state, ai->d_kind, achildren);
      }
      if (ai->d_isOverloaded)
      {
        Trace("overload") << "Use overload when constructing " << k << " "
                          << children << std::endl;
        std::vector<Expr>& ov = state.d_overloads[ai->d_overloadName];
        Assert(ov.size() >= 2);
        Expr ret = state.getOverloadInternal(ov, children, nullptr, true);
        if (!ret.isNull())
        {
          Trace("overload") << "...found overload " << ret << std::endl;
          return ret;
        }
        Warning() << "No overload found when constructing application "
                  << children << std::endl;
      }
    }
    return mkApply(state, children);
  }
  if (isLiteralOp(k))
  {
    return state.mkLiteralOp(k, children);
  }
  if (k == Kind::AS_RETURN)
  {
    // (as nil (List Int)) --> (_ nil (List Int))
    Attr ck = state.getConstructorKind(vchildren[0]);
    if ((ck == Attr::AMB_DATATYPE_CONSTRUCTOR || ck == Attr::AMB)
        && children.size() == 2)
    {
      Trace("overload") << "...type arg for ambiguous constructor"
                        << std::endl;
      return mkExpr(state, Kind::APPLY_OPAQUE, {children[0], children[1]});
    }
    // We don't support other uses of `as` for symbol disambiguation yet, and
    // fall through to build the raw AS_RETURN term below.
  }
  else if (k == Kind::AS)
  {
    // If it has 2 children, process it, otherwise make the raw AS term below.
    if (vchildren.size() == 2)
    {
      Trace("overload") << "process eo::as " << children[0] << " "
                        << children[1] << std::endl;
      AppInfo* ai = state.getAppInfo(vchildren[0]);
      std::pair<std::vector<Expr>, Expr> ftype = children[1].getFunctionType();
      Expr reto;
      std::vector<Expr> dummyChildren;
      dummyChildren.push_back(children[1]);
      for (const Expr& t : ftype.first)
      {
        dummyChildren.emplace_back(state.mkSymbol(Kind::CONST, "tmp", t));
      }
      if (ai != nullptr && ai->d_isOverloaded)
      {
        Trace("overload") << "...overloaded" << std::endl;
        std::vector<Expr>& ov = state.d_overloads[ai->d_overloadName];
        Assert(ov.size() >= 2);
        reto = state.getOverloadInternal(
            ov, dummyChildren, ftype.second.getValue(), false);
      }
      else
      {
        Trace("overload") << "...not overloaded" << std::endl;
        reto = state.getOverloadInternal(
            {children[0]}, dummyChildren, ftype.second.getValue(), false);
      }
      if (!reto.isNull())
      {
        Trace("overload") << "...found overload " << reto << " "
                          << state.getTypeChecker().getType(reto)
                          << std::endl;
        return reto;
      }
    }
  }
  return Expr(state.mkExprInternal(k, vchildren));
}

}  // namespace expr_builder
}  // namespace ethos
