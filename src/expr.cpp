#include "expr.h"

#include <set>
#include <iostream>
#include "state.h"

namespace alfc {
  
State* ExprValue::d_state = nullptr;

ExprValue::ExprValue() : d_kind(Kind::NONE), d_flags(0) {}

ExprValue::ExprValue(Kind k,
      const std::vector<std::shared_ptr<ExprValue>>& children) : d_kind(k), d_children(children), d_flags(0){}
ExprValue::~ExprValue() {}

bool ExprValue::isNull() const { return d_kind==Kind::NONE; }
  
Kind ExprValue::getKind() const { return d_kind; }

std::vector<std::shared_ptr<ExprValue>>& ExprValue::getChildren() { return d_children; }

size_t ExprValue::getNumChildren() const
{
  return d_children.size();
}
std::shared_ptr<ExprValue> ExprValue::operator[](size_t i) const
{
  return d_children[i];
}

bool ExprValue::isEvaluatable()
{
  computeFlags();
  return getFlag(Flag::IS_EVAL);
}

bool ExprValue::isGround()
{
  computeFlags();
  return !getFlag(Flag::IS_NON_GROUND);
}

bool ExprValue::isProgEvaluatable()
{
  computeFlags();
  return getFlag(Flag::IS_PROG_EVAL);
}

bool ExprValue::isCompiled()
{
  // this is set manually
  return getFlag(Flag::IS_COMPILED);
}

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
    std::vector<Expr>& children = cur->d_children;
    if (children.empty())
    {
      bool isNonGround = (ck==Kind::PARAM);
      cur->setFlag(Flag::IS_EVAL, false);
      cur->setFlag(Flag::IS_NON_GROUND, isNonGround);
      visit.pop_back();
    }
    else if (visited.find(cur)==visited.end())
    {
      visited.insert(cur);
      for (Expr& c : children)
      {
        if (!c->getFlag(Flag::IS_FLAGS_COMPUTED))
        {
          visit.push_back(c.get());
        }
      }
    }
    else
    {
      visit.pop_back();
      if (ck==Kind::APPLY)
      {
        Kind cck = children[0]->getKind();
        if (cck==Kind::PROGRAM_CONST)
        {
          cur->setFlag(Flag::IS_PROG_EVAL, true);
          cur->setFlag(Flag::IS_EVAL, true);
        }
      }
      else if (isLiteralOp(ck))
      {
        // requires type and literal operator kinds evaluate
        cur->setFlag(Flag::IS_EVAL, true);
      }
      for (Expr& c : children)
      {
        if (c->getFlag(Flag::IS_NON_GROUND))
        {
          cur->setFlag(Flag::IS_NON_GROUND, true);
        }
        if (c->getFlag(Flag::IS_EVAL))
        {
          cur->setFlag(Flag::IS_EVAL, true);
        }
        if (c->getFlag(Flag::IS_PROG_EVAL))
        {
          cur->setFlag(Flag::IS_PROG_EVAL, true);
        }
      }
    }
  }
  while (!visit.empty());
}

std::string ExprValue::getSymbol() const
{
  Literal * l = d_state->getLiteral(this);
  if (l!=nullptr)
  {
    return l->toString();
  }
  return "";
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

std::map<const ExprValue*, size_t> ExprValue::computeLetBinding(const std::shared_ptr<ExprValue>& e, 
                                                                std::vector<const ExprValue*>& ll)
{
  size_t idc = 0;
  std::map<const ExprValue*, size_t> lbind;
  std::unordered_set<const ExprValue*> visited;
  std::vector<const ExprValue*> visit;
  std::vector<const ExprValue*> llv;
  const ExprValue* cur;
  visit.push_back(e.get());
  do
  {
    cur = visit.back();
    visit.pop_back();
    const std::vector<Expr>& children = cur->d_children;
    if (children.empty())
    {
      continue;
    }
    if (visited.find(cur)==visited.end())
    {
      llv.push_back(cur);
      visited.insert(cur);
      for (const Expr& c : children)
      {
        visit.push_back(c.get());
      }
      continue;
    }
    if (lbind.find(cur)==lbind.end())
    {
      lbind[cur] = idc;
      idc++;
    }
  }while(!visit.empty());
  for (size_t i=0, lsize = llv.size(); i<lsize; i++)
  {
    const ExprValue* l = llv[lsize-1-i];
    if (lbind.find(l)!=lbind.end())
    {
      ll.push_back(l);
    }
  }
  return lbind;
}

void ExprValue::printDebugInternal(const ExprValue* e, 
                                   std::ostream& os,
                                   std::map<const ExprValue*, size_t>& lbind)
{
  std::map<const ExprValue*, size_t>::iterator itl;
  std::vector<std::pair<const ExprValue*, size_t>> visit;
  std::pair<const ExprValue*, size_t> cur;
  visit.emplace_back(e, 0);
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
      if (cur.first->getNumChildren()==0)
      {
        Literal * l = d_state->getLiteral(cur.first);
        if (l!=nullptr)
        {
          switch (l->d_tag)
          {
            case Literal::BITVECTOR:os << "#b" << l->toString();break;
            case Literal::STRING:os << "\"" << l->toString() << "\"";break;
            case Literal::SYMBOL:
              // symbols must be quoted if they have illegal characters
              os << quoteSymbol(l->toString());
              break;
            default:os << l->toString();break;
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
        if (k!=Kind::APPLY && k!=Kind::PAIR)
        {
          os <<  kindToTerm(k) << " ";
        }
        visit.back().second++;
        visit.emplace_back((*cur.first)[0].get(), 0);
      }
    }
    else if (cur.second==cur.first->getNumChildren())
    {
      os << ")";
      visit.pop_back();
    }
    else
    {
      os << " ";
      visit.back().second++;
      visit.emplace_back((*cur.first)[cur.second].get(), 0);
    }
  } while (!visit.empty());
}

void ExprValue::printDebug(const std::shared_ptr<ExprValue>& e, std::ostream& os)
{
  std::map<const ExprValue*, size_t> lbind;
  std::string cparen;
  if (d_state->getOptions().d_printLet)
  {
    std::vector<const ExprValue*> ll;
    lbind = computeLetBinding(e, ll);
    std::stringstream osc;
    for (const ExprValue* l : ll)
    {
      size_t id = lbind[l];
      os << "(let ((_v" << id << " ";
      lbind.erase(l);
      printDebugInternal(l, os, lbind);
      lbind[l] = id;
      os << ")) ";
      osc << ")";
    }
    cparen = osc.str();
  }
  printDebugInternal(e.get(), os, lbind);
  os << cparen;
}


std::vector<Expr> ExprValue::getVariables(const Expr& e)
{
  std::vector<Expr> es{e};
  return getVariables(es);
}

std::vector<Expr> ExprValue::getVariables(const std::vector<Expr>& es)
{
  std::vector<Expr> ret;
  std::unordered_set<Expr> visited;
  std::vector<Expr> toVisit;
  toVisit = es;
  Expr cur;
  while (!toVisit.empty())
  {
    cur = toVisit.back();
    toVisit.pop_back();
    if (cur->isGround())
    {
      continue;
    }
    if (visited.find(cur)!=visited.end())
    {
      continue;
    }
    visited.insert(cur);
    if (cur->getKind()==Kind::PARAM)
    {
      ret.push_back(cur);
      continue;
    }
    toVisit.insert(toVisit.end(), cur->d_children.begin(), cur->d_children.end());
  }
  return ret;
}

bool ExprValue::hasVariable(const Expr& e, const std::unordered_set<Expr>& vars)
{
  if (vars.empty())
  {
    return false;
  }
  std::unordered_set<Expr> visited;
  std::vector<Expr> toVisit;
  toVisit.push_back(e);
  Expr cur;
  do
  {
    cur = toVisit.back();
    toVisit.pop_back();
    if (e->isGround())
    {
      continue;
    }
    if (visited.find(cur)!=visited.end())
    {
      continue;
    }
    visited.insert(cur);
    if (cur->getKind()==Kind::PARAM)
    {
      if (vars.find(cur)!=vars.end())
      {
        return true;
      }
    }
    toVisit.insert(toVisit.end(), cur->d_children.begin(), cur->d_children.end());
  }while (!toVisit.empty());
  return false;
}

std::ostream& operator<<(std::ostream& out, const Expr& e)
{
  ExprValue::printDebug(e, out);
  return out;
}

}  // namespace alfc

