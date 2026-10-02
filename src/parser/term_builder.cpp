/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "parser/term_builder.h"

#include "base/check.h"
#include "base/output.h"

namespace ethos {

TermBuilder::TermBuilder(State& s) : d_state(s), d_tc(s.getTypeChecker()) {}

Expr TermBuilder::mkExpr(Kind k,
                         const std::vector<Expr>& children,
                         const Overloads& overloads)
{
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  if (k==Kind::APPLY)
  {
    Assert(!children.empty());
    // see if there is a special way of building terms for the head
    ExprValue* hd = vchildren[0];
    AppInfo* ai = d_state.getAppInfo(hd);
    if (ai!=nullptr && ai->d_kind!=Kind::NONE)
    {
      Trace("state-debug") << "Process builtin app " << ai->d_kind << std::endl;
      if (ai->d_kind==Kind::FUNCTION_TYPE)
      {
        // functions (from parsing) are flattened here
        std::vector<Expr> achildren(children.begin()+1, children.end()-1);
        return d_state.mkFunctionType(achildren, children.back());
      }
      else if (ai->d_kind == Kind::APPLY)
      {
        // Applications (_ f ...) do *not* recursively desugar.
        // remove the dummy operator "_"
        vchildren.erase(vchildren.begin(), vchildren.begin() + 1);
        // return the curried version
        return Expr(vchildren.size() > 2
                        ? d_state.mkApplyInternal(vchildren)
                        : d_state.mkExprInternal(Kind::APPLY, vchildren));
      }
      // another builtin operator, possibly APPLY
      std::vector<Expr> achildren(children.begin()+1, children.end());
      Overloads aoverloads;
      if (overloads.size() > 1)
      {
        aoverloads.insert(
            aoverloads.end(), overloads.begin() + 1, overloads.end());
      }
      // must call mkExpr again, since we may auto-evaluate
      return mkExpr(ai->d_kind, achildren, aoverloads);
    }
    if (!overloads.empty() && overloads[0] != nullptr)
    {
      Trace("overload") << "Use overload when constructing " << k << " " << children << std::endl;
      const std::vector<Expr>& ov = *overloads[0];
      Assert (ov.size()>=2);
      Expr ret = getOverloadInternal(ov, children, nullptr, true);
      if (!ret.isNull())
      {
        Trace("overload") << "...found overload " << ret << std::endl;
        return ret;
      }
      Warning() << "No overload found when constructing application "
                << children << std::endl;
    }
    if (ai!=nullptr)
    {
      // Compute the "constructor term" for the operator, which may involve
      // type inference. We store the constructor term in consTerm and operator
      // in hdTerm, where notice hdTerm is of kind PARAMETERIZED if consTerm
      // (prior to resolution) was PARAMETERIZED. So, for example, applying
      // `bvor` to `a` of type `(BitVec 4)` results in
      //   consTerm := #b0000.
      Expr consTerm = d_tc.computeConstructorTermInternal(ai, children);
      Expr ret = mkApplyAttr(ai, vchildren, consTerm);
      if (!ret.isNull())
      {
        return ret;
      }
    }
  }
  else if (k == Kind::AS_RETURN)
  {
    // (as nil (List Int)) --> (_ nil (List Int))
    Attr ck = d_state.getAttributeKind(vchildren[0]);
    if ((ck == Attr::AMB_DATATYPE_CONSTRUCTOR || ck == Attr::AMB)
        && children.size() == 2)
    {
      Trace("overload") << "...type arg for ambiguous constructor" << std::endl;
      return d_state.mkExpr(Kind::APPLY_OPAQUE, {children[0], children[1]});
    }
    // note we don't support other uses of `as` for symbol disambiguation yet,
    // we fallthrough and construct the bogus term of kind AS_RETURN.
  }
  else if (k==Kind::AS)
  {
    // if it has 2 children, process it, otherwise we make the bogus term of
    // kind AS below
    if (vchildren.size()==2)
    {
      Trace("overload") << "process eo::as " << children[0] << " " << children[1] << std::endl;
      std::pair<std::vector<Expr>, Expr> ftype = children[1].getFunctionType();
      Expr reto;
      // look up the overload
      std::vector<Expr> dummyChildren;
      dummyChildren.push_back(children[1]);
      for (const Expr& t : ftype.first)
      {
        dummyChildren.emplace_back(d_state.mkSymbol(Kind::CONST, "tmp", t));
      }
      if (!overloads.empty() && overloads[0] != nullptr)
      {
        Trace("overload") << "...overloaded" << std::endl;
        const std::vector<Expr>& ov = *overloads[0];
        Assert (ov.size()>=2);
        reto = getOverloadInternal(
            ov, dummyChildren, ftype.second.getValue(), false);
      }
      else
      {
        Trace("overload") << "...not overloaded" << std::endl;
        reto = getOverloadInternal(
            {children[0]}, dummyChildren, ftype.second.getValue(), false);
      }
      if (!reto.isNull())
      {
        Trace("overload") << "...found overload " << reto << " " << d_tc.getType(reto) << std::endl;
        return reto;
      }
    }
    // otherwise construct the bogus term of kind AS
    return Expr(d_state.mkExprInternal(k, vchildren));
  }
  // otherwise, the state constructs the term
  return d_state.mkExpr(k, children);
}

Expr TermBuilder::mkBinderList(const ExprValue* ev, const std::vector<Expr>& vs)
{
  Assert (!vs.empty());
  std::vector<Expr> vlist;
  vlist.push_back(d_state.getAttributeTerm(ev));
  vlist.insert(vlist.end(), vs.begin(), vs.end());
  return mkExpr(Kind::APPLY, vlist);
}

Expr TermBuilder::mkLetBinderList(
    const ExprValue* ev, const std::vector<std::pair<Expr, Expr>>& lls)
{
  Assert (!lls.empty());
  Expr cons = d_state.getAttributeTerm(ev);
  Assert (cons.getKind()==Kind::TUPLE && cons.getNumChildren()==2);
  Expr pairCons = cons[0];
  Expr listCons = cons[1];
  std::vector<Expr> vs;
  for (const std::pair<Expr, Expr>& ll : lls)
  {
    vs.emplace_back(mkExpr(Kind::APPLY, {pairCons, ll.first, ll.second}));
  }
  std::vector<Expr> vlist;
  vlist.push_back(listCons);
  vlist.insert(vlist.end(), vs.begin(), vs.end());
  return mkExpr(Kind::APPLY, vlist);
}

Expr TermBuilder::mkPremiseList(const Expr& plCons,
                                const std::vector<Expr>& premises,
                                std::ostream* err)
{
  // this collects the premises (pf F1) ... (pf Fn) and constructs
  // e.g. (pf (and F1 ... Fn)), where and is the operator marked with
  // :premise-list.
  std::vector<Expr> achildren;
  achildren.push_back(plCons);
  for (const Expr& e : premises)
  {
    // should be proofs
    if (e.getKind() != Kind::PROOF)
    {
      if (err)
      {
        (*err) << "Provided premise is not a proof" << std::endl;
      }
      return d_null;
    }
    achildren.push_back(e[0]);
  }
  Expr ap;
  if (achildren.size()==1)
  {
    // the nil terminator if applied to empty list
    Attr ck = d_state.getAttributeKind(plCons.getValue());
    if (isListNilAttr(ck))
    {
      ap = d_state.getAttributeTerm(plCons.getValue());
    }
    else
    {
      if (err)
      {
        (*err) << "Premise list constructor " << plCons
               << " has no nil element" << std::endl;
      }
      return d_null;
    }
  }
  else
  {
    ap = mkExpr(Kind::APPLY, achildren);
  }
  // collects to a proof
  return d_state.mkProof(ap);
}

Expr TermBuilder::mkApplyAttr(AppInfo* ai,
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
          if (d_state.getAttributeKind(curr) != Attr::LIST)
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
                  Expr(d_state.mkExprInternal(Kind::EVAL_TYPE_OF, {vchildren[1]}));
              curr = d_state.mkExprInternal(Kind::EVAL_NIL,
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
          if (isNil && d_state.getAttributeKind(cc[nextIndex]) == Attr::LIST)
          {
            curr = d_state.mkExprInternal(Kind::EVAL_LIST_CONCAT, cc);
          }
          else
          {
            nlistTerms++;
            curr = d_state.mkApplyInternal(cc);
          }
          i++;
        }
        // if we are a non-singleton list with fewer than 2 non-list children
        if (isNsNil && nlistTerms<2)
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
          return mkExpr(Kind::EVAL_LIST_SINGLETON_ELIM, ccse);
        }
        Trace("type_checker")
            << "...return for " << Expr(vchildren[0]) << std::endl;
        return Expr(curr);
      }
      else
      {
        // Otherwise we are applying the operator to zero arguments. This
        // can never occur in standard parsing since it is not possible
        // to apply a function to zero arguments. However, this case may
        // arise if e.g. a pairwise or chainable operator is applied to
        // exactly one argument, e.g. (distinct t) is equivalent to true.
        return consTerm;
      }
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
        cchildren.emplace_back(d_state.mkApplyInternal(cc));
      }
      if (cchildren.size() == 2)
      {
        // no need to chain
        return cchildren[1];
      }
      // note this could loop
      return mkExpr(Kind::APPLY, cchildren);
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
          cchildren.emplace_back(d_state.mkApplyInternal(cc));
        }
      }
      if (cchildren.size() == 2)
      {
        // no need to chain
        return cchildren[1];
      }
      // note this could loop
      return mkExpr(Kind::APPLY, cchildren);
    }
    break;
    case Attr::ARG_LIST:
    {
      Expr argList;
      // If there is only one argument, and it was marked :list, then it is
      // not desugared.
      if (vchildren.size() == 2 && d_state.getAttributeKind(vchildren[1]) == Attr::LIST)
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
        argList = mkExpr(Kind::APPLY, cchildren);
      }
      return Expr(
          d_state.mkExprInternal(Kind::APPLY, {vchildren[0], argList.getValue()}));
    }
    break;
    case Attr::OPAQUE:
    {
      // determine how many opaque children
      Expr hdt = Expr(hd);
      const Expr& t = d_tc.getType(hdt);
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
        // Note we do not curry APPLY_OPAQUE applications, as they are simpler
        // to reason about in flattened form.
        Assert (nargs < vchildren.size());
        std::vector<ExprValue*> ochildren(vchildren.begin(),
                                          vchildren.begin() + 1 + nargs);
        Expr op = Expr(d_state.mkExprInternal(Kind::APPLY_OPAQUE, ochildren));
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
          return Expr(d_state.mkApplyInternal(rchildren));
        }
        return Expr(d_state.mkExprInternal(Kind::APPLY, rchildren));
      }
    }
    default: break;
  }
  return d_null;
}

Expr TermBuilder::getOverloadInternal(const std::vector<Expr>& overloads,
                                const std::vector<Expr>& children,
                                const ExprValue* retType,
                                bool retApply)
{
  Assert (!overloads.empty());
  Trace("overload") << "Get overload" << std::endl;
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  // try overloads in order until one is found
  for (size_t i=0, noverloads = overloads.size(); i<noverloads; i++)
  {
    // search in reverse order, i.e. the last bound symbol takes precendence
    size_t ii = (noverloads-1)-i;
    ExprValue* hd = overloads[ii].getValue();
    vchildren[0] = hd;
    Expr hde(hd);
    Trace("overload") << "Try " << d_tc.getType(hde) << std::endl;
    AppInfo* ai = d_state.getAppInfo(hd);
    Expr x;
    if (ai != nullptr)
    {
      Trace("overload") << "...has property " << ai->d_attrCons << std::endl;
      Expr consTerm = d_tc.computeConstructorTermInternal(ai, children);
      x = mkApplyAttr(ai, vchildren, consTerm);
    }
    if (x.isNull())
    {
      x = Expr(vchildren.size() > 2 ? d_state.mkApplyInternal(vchildren)
                                    : d_state.mkExprInternal(Kind::APPLY, vchildren));
    }
    Expr t = d_tc.getType(x);

    Trace("overload") << "type of " << x << " is " << t << std::endl;
    // if term is well-formed, and matches the return type if it exists
    if (!t.isNull() && (retType==nullptr || retType==t.getValue()))
    {
      Trace("overload") << "...return success" << std::endl;
      // an overloaded define macro is beta-reduced eagerly, as in mkExpr
      if (retApply && hd->getKind() == Kind::LAMBDA)
      {
        Expr ret = d_state.mkBetaReduceInternal(vchildren);
        if (!ret.isNull())
        {
          return ret;
        }
      }
      // return the operator, do not check the remainder
      return retApply ? x : overloads[ii];
    }
  }
  // otherwise, none found, return null
  return d_null;
}

}  // namespace ethos
