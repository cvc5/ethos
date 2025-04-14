/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "expr.h"

#include <iostream>
#include <set>

#include "base/output.h"
#include "state.h"

namespace ethos {

ExprValue ExprValue::s_null;
State* ExprValue::d_state = nullptr;

ExprValue::ExprValue() : d_kind(Kind::NONE), d_flags(0), d_rc(0) {}

ExprValue::ExprValue(Kind k, const std::vector<ExprValue*>& children)
    : d_kind(k), d_children(children), d_flags(0), d_rc(0)
{
  for (ExprValue * c : children)
  {
    c->inc();
  }
}
ExprValue::~ExprValue() 
{
  for (ExprValue * c : d_children)
  {
    c->dec();
  }
}

bool ExprValue::isNull() const { return d_kind==Kind::NONE; }
  
Kind ExprValue::getKind() const { return d_kind; }

const std::vector<ExprValue*>& ExprValue::getChildren() const { return d_children; }

size_t ExprValue::getNumChildren() const
{
  return d_children.size();
}
ExprValue* ExprValue::operator[](size_t i) const { return d_children[i]; }

void ExprValue::computeFlags()
{
  if (getFlag(Flag::IS_FLAGS_COMPUTED))
  {
    return;
  }
  std::unordered_set<ExprValue*> visited;
  std::vector<ExprValue*> visit;
  visit.emplace_back(this);
  ExprValue * cur;
  do
  {
    cur = visit.back();
    cur->setFlag(Flag::IS_FLAGS_COMPUTED, true);
    Kind ck = cur->getKind();
    std::vector<ExprValue*>& children = cur->d_children;
    if (children.empty())
    {
      bool isEval = (ck == Kind::PROGRAM_CONST || ck == Kind::ORACLE);
      bool isNonGround = (ck==Kind::PARAM);
      cur->setFlag(Flag::IS_EVAL, isEval);
      cur->setFlag(Flag::IS_NON_GROUND, isNonGround);
      visit.pop_back();
    }
    else if (visited.find(cur)==visited.end())
    {
      visited.insert(cur);
      for (ExprValue* c : children)
      {
        if (!c->getFlag(Flag::IS_FLAGS_COMPUTED))
        {
          visit.push_back(c);
        }
      }
    }
    else
    {
      visit.pop_back();
      if (isLiteralOp(ck))
      {
        // literal operator kinds are evaluatable
        cur->setFlag(Flag::IS_EVAL, true);
      }
      // flags are a union of the flags of the children
      for (ExprValue* c : children)
      {
        cur->d_flags |= static_cast<uint8_t>(c->d_flags);
      }
    }
  }
  while (!visit.empty());
}
bool ExprValue::isEvaluatable()
{
  computeFlags();
  return getFlag(ExprValue::Flag::IS_EVAL);
}

bool ExprValue::isGround()
{
  computeFlags();
  return !getFlag(ExprValue::Flag::IS_NON_GROUND);
}

void ExprValue::dec()
{
  d_rc--;
  if (d_rc == 0)
  {
    Assert(d_state != nullptr);
    d_state->markDeleted(this);
  }
}

Expr::Expr() { d_value = &ExprValue::s_null; }
Expr::Expr(const ExprValue* ev)
{
  if (ev == nullptr)
  {
    d_value = &ExprValue::s_null;
  }
  else
  {
    d_value = const_cast<ExprValue*>(ev);
    d_value->inc();
  }
}
Expr::Expr(const Expr& e)
{
  d_value = e.d_value;
  Assert(d_value != nullptr);
  if (!d_value->isNull())
  {
    d_value->inc();
  }
}
Expr::~Expr()
{
  Assert(d_value != nullptr);
  if (!d_value->isNull())
  {
    d_value->dec();
    d_value = nullptr;
  }
}

bool Expr::isNull() const { return d_value->isNull(); }
bool Expr::isEvaluatable() const { return d_value->isEvaluatable(); }
bool Expr::isGround() const { return d_value->isGround(); }
std::string Expr::getSymbol() const
{
  const Literal * l = d_value->asLiteral();
  if (l != nullptr)
  {
    return l->toString();
  }
  return "";
}

ExprValue* Expr::getValue() const { return d_value; }

std::pair<std::vector<Expr>, Expr> Expr::getFunctionType() const
{
  Expr et = *this;
  std::vector<Expr> args;
  while (et.getKind()==Kind::FUNCTION_TYPE)
  {
    size_t nchild = et.getNumChildren();
    for (size_t i=0; i<nchild-1; i++)
    {
      args.push_back(et[i]);
    }
    et = et[nchild-1];
    // strip off requires
    while (et.getKind()==Kind::EVAL_REQUIRES)
    {
      et = et[2];
    }
  }
  return std::pair<std::vector<Expr>, Expr>(args, et);
}

size_t Expr::getFunctionArity() const
{
  std::pair<std::vector<Expr>, Expr> ftype = getFunctionType();
  return ftype.first.size();
}

/**
 * SMT-LIB 2 quoting for symbols
 */
std::string quoteSymbol(const std::string& s)
{
  if (s.empty())
  {
    return "||";
  }

  // this is the set of SMT-LIBv2 permitted characters in "simple" (non-quoted)
  // symbols
  if (s.find_first_not_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
                          "0123456789~!@$%^&*_-+=<>.?/")
          == std::string::npos
      && (s[0] < '0' || s[0] > '9'))
  {
    return s;
  }
  std::string tmp = s;
  if (s.front() == '|' && s.back() == '|' && s.length() > 1)
  {
    // if s is already surrounded with vertical bars, we need to check the
    // characters between them
    tmp = s.substr(1, s.length() - 2);
  }

  // must quote the symbol, but it cannot contain | or \, we turn those into _
  size_t p;
  while ((p = tmp.find_first_of("\\|")) != std::string::npos)
  {
    tmp = tmp.replace(p, 1, "_");
  }
  return "|" + tmp + "|";
}

std::map<const ExprValue*, size_t> Expr::computeLetBinding(
    const Expr& e, std::vector<Expr>& ll)
{
  std::map<const ExprValue*, size_t> lcount;
  std::unordered_set<const ExprValue*> visited;
  std::vector<Expr> visit;
  std::vector<Expr> llv;
  Expr cur;
  visit.push_back(e);
  do
  {
    cur = visit.back();
    if (cur.getNumChildren() == 0)
    {
      visit.pop_back();
      continue;
    }
    const ExprValue* cv = cur.getValue();
    if (visited.find(cv) == visited.end())
    {
      visited.insert(cv);
      for (size_t i = 0, nchildren = cur.getNumChildren(); i < nchildren; i++)
      {
        visit.push_back(cur[i]);
      }
      continue;
    }
    visit.pop_back();
    // add to vector, which is done after all subterms of cv are added to llv
    if (lcount.find(cv) == lcount.end())
    {
      llv.push_back(cur);
    }
    lcount[cv]++;
  }while(!visit.empty());
  // go back and only keep the ones that were found more than once.
  std::map<const ExprValue*, size_t> lbind;
  size_t idc = 0;
  for (size_t i=0, lsize = llv.size(); i<lsize; i++)
  {
    const Expr& l = llv[i];
    const ExprValue* lv = l.getValue();
    if (lcount[lv] > 1)
    {
      ll.push_back(l);
      lbind[lv] = idc;
      idc++;
    }
  }
  return lbind;
}

void Expr::printDebugInternal(const Expr& e,
                              std::ostream& os,
                              std::map<const ExprValue*, size_t>& lbind)
{
  std::map<const ExprValue*, size_t>::iterator itl;
  std::vector<std::pair<ExprValue*, size_t>> visit;
  std::pair<ExprValue*, size_t> cur;
  visit.emplace_back(e.getValue(), 0);
  do {
    cur = visit.back();
    if (cur.second==0)
    {
      itl = lbind.find(cur.first);
      if (itl!=lbind.end())
      {
        os << "_v" << itl->second;
        visit.pop_back();
        continue;
      }
      Kind k = cur.first->getKind();
      if (cur.first->getNumChildren() == 0)
      {
        const Literal* l = cur.first->asLiteral();
        if (l!=nullptr)
        {
          switch (k)
          {
            case Kind::HEXADECIMAL:os << "#x" << l->toString();break;
            case Kind::BINARY:os << "#b" << l->toString();break;
            case Kind::STRING:os << "\"" << l->toString() << "\"";break;
            case Kind::DECIMAL:
              // currently don't have a way to print decimals natively, just
              // use attribute
              os << "(! " << l->toString() << " :decimal)";
              break;
            default:
              if (isSymbol(k))
              {
                // symbols must be quoted if they have illegal characters
                os << quoteSymbol(l->toString());
              }
              else
              {
                os << l->toString();
              }
              break;
          }
        }
        else
        {
          os << kindToTerm(k);
        }
        visit.pop_back();
      }
      else
      {
        os << "(";
        if (k!=Kind::APPLY && k!=Kind::TUPLE)
        {
          os << kindToTerm(k) << " ";
        }
        visit.back().second++;
        visit.emplace_back((*cur.first)[0], 0);
      }
    }
    else if (cur.second == cur.first->getNumChildren())
    {
      os << ")";
      visit.pop_back();
    }
    else
    {
      Assert (cur.second<cur.first->getNumChildren());
      os << " ";
      visit.back().second++;
      visit.emplace_back((*cur.first)[cur.second], 0);
    }
  } while (!visit.empty());
}

void Expr::printDebug(const Expr& e, std::ostream& os)
{
  std::map<const ExprValue*, size_t> lbind;
  std::string cparen;
  if (ExprValue::d_state->getOptions().d_printDag)
  {
    std::vector<Expr> ll;
    lbind = computeLetBinding(e, ll);
    std::stringstream osc;
    for (const Expr& l : ll)
    {
      const ExprValue* lv = l.getValue();
      size_t id = lbind[lv];
      os << "(eo::define ((_v" << id << " ";
      lbind.erase(lv);
      printDebugInternal(l, os, lbind);
      lbind[lv] = id;
      os << ")) ";
      osc << ")";
    }
    cparen = osc.str();
  }
  printDebugInternal(e, os, lbind);
  os << cparen;
}

std::vector<Expr> Expr::getVariables(const Expr& e)
{
  std::vector<Expr> es{e};
  return getVariables(es);
}

std::vector<Expr> Expr::getVariables(const std::vector<Expr>& es)
{
  std::vector<Expr> ret;
  std::unordered_set<const ExprValue*> visited;
  std::vector<Expr> toVisit;
  toVisit = es;
  Expr cur;
  while (!toVisit.empty())
  {
    cur = toVisit.back();
    toVisit.pop_back();
    if (cur.isGround())
    {
      continue;
    }
    const ExprValue* cv = cur.getValue();
    if (visited.find(cv) != visited.end())
    {
      continue;
    }
    visited.insert(cv);
    if (cur.getKind() == Kind::PARAM)
    {
      ret.push_back(cur);
      continue;
    }
    for (size_t i = 0, nchildren = cur.getNumChildren(); i < nchildren; i++)
    {
      toVisit.push_back(cur[i]);
    }
  }
  return ret;
}

size_t Expr::getNumChildren() const { return d_value->getNumChildren(); }

Expr Expr::operator[](size_t i) const { return Expr(d_value->d_children[i]); }

Expr& Expr::operator=(const Expr& e)
{
  if (d_value != e.d_value)
  {
    if (!isNull())
    {
      d_value->dec();
    }
    d_value = e.d_value;
    if (!isNull())
    {
      d_value->inc();
    }
  }
  return *this;
}

bool Expr::operator==(const Expr& e) const { return d_value == e.d_value; }
bool Expr::operator!=(const Expr& e) const { return d_value != e.d_value; }
Kind Expr::getKind() const { return d_value->getKind(); }

bool Expr::hasVariable(const Expr& e,
                       const std::unordered_set<const ExprValue*>& vars)
{
  if (vars.empty())
  {
    return false;
  }
  std::unordered_set<const ExprValue*> visited;
  std::vector<Expr> toVisit;
  toVisit.push_back(e);
  Expr cur;
  do
  {
    cur = toVisit.back();
    toVisit.pop_back();
    if (e.isGround())
    {
      continue;
    }
    const ExprValue* cv = cur.getValue();
    if (visited.find(cv) != visited.end())
    {
      continue;
    }
    visited.insert(cv);
    if (cur.getKind() == Kind::PARAM)
    {
      if (vars.find(cv) != vars.end())
      {
        return true;
      }
    }
    for (size_t i = 0, nchildren = cur.getNumChildren(); i < nchildren; i++)
    {
      toVisit.push_back(cur[i]);
    }
  }while (!toVisit.empty());
  return false;
}

std::ostream& operator<<(std::ostream& out, const Expr& e)
{
  Expr::printDebug(e, out);
  return out;
}
std::ostream& operator<<(std::ostream& out, const std::vector<ExprValue*>& es)
{
  out << "[";
  bool firstTime = true;
  for (ExprValue* e : es)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      out << " ";
    }
    out << Expr(e);
  }
  out << "]";
  return out;
}

std::ostream& operator<<(std::ostream& out, const Ctx& c)
{
  out << "[";
  bool firstTime = true;
  for (const std::pair<ExprValue* const, ExprValue*>& cc : c)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      out << ", ";
    }
    out << Expr(cc.first) << " -> " << Expr(cc.second);
  }
  out << "]";
  return out;
}

}  // namespace ethos
