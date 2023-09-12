#include "expr.h"

#include <set>
#include <iostream>
#include "state.h"

namespace alfc {
  
ExprValue ExprValue::s_null;

ExprValue::ExprValue() : d_kind(Kind::NONE), d_flags(0) {}

ExprValue::ExprValue(Kind k,
      const std::vector<ExprValue*>& children) : d_kind(k), d_children(children), d_flags(0), d_rc(0){}
ExprValue::~ExprValue() {}

bool ExprValue::isNull() const { return d_kind==Kind::NONE; }
  
Kind ExprValue::getKind() const { return d_kind; }

std::vector<ExprValue*>& ExprValue::getChildren() { return d_children; }

size_t ExprValue::getNumChildren() const
{
  return d_children.size();
}
ExprValue* ExprValue::operator[](size_t i) const
{
  return d_children[i];
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
    std::vector<ExprValue *>& children = cur->d_children;
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
      for (ExprValue * c : children)
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
      if (ck==Kind::APPLY)
      {
        Kind cck = children[0]->getKind();
        if (cck==Kind::PROGRAM_CONST || cck==Kind::ORACLE)
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
      for (ExprValue * c : children)
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


void ExprValue::inc()
{
  d_rc++;
}
void ExprValue::dec()
{
  d_rc--;
}

State* Expr::d_state = nullptr;

Expr::Expr()
{
  d_value = &ExprValue::s_null;
}
Expr::Expr(const ExprValue* ev)
{
  if (ev==nullptr)
  {
    d_value = &ExprValue::s_null;
  }
  else
  {
    d_value = const_cast<ExprValue*>(ev);
    d_value->inc();
  }
}
Expr::~Expr()
{
  d_value = nullptr;
}

bool Expr::isNull() const
{
  return d_value==&ExprValue::s_null;
}

bool Expr::isEvaluatable() const
{
  d_value->computeFlags();
  return d_value->getFlag(ExprValue::Flag::IS_EVAL);
}

bool Expr::isGround() const
{
  d_value->computeFlags();
  return !d_value->getFlag(ExprValue::Flag::IS_NON_GROUND);
}

bool Expr::isProgEvaluatable() const
{
  d_value->computeFlags();
  return d_value->getFlag(ExprValue::Flag::IS_PROG_EVAL);
}

bool Expr::isCompiled() const
{
  // this is set manually
  return d_value->getFlag(ExprValue::Flag::IS_COMPILED);
}

std::string Expr::getSymbol() const
{
  return d_state->getSymbol(d_value);
}

ExprValue * Expr::getValue() const
{
  return d_value;
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

std::map<const ExprValue*, size_t> Expr::computeLetBinding(const Expr& e, 
                                                                std::vector<Expr>& ll)
{
  size_t idc = 0;
  std::map<const ExprValue*, size_t> lbind;
  std::unordered_set<const ExprValue*> visited;
  std::vector<Expr> visit;
  std::vector<Expr> llv;
  Expr cur;
  visit.push_back(e);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (cur.getNumChildren()==0)
    {
      continue;
    }
    const ExprValue * cv = cur.getValue();
    if (visited.find(cv)==visited.end())
    {
      visited.insert(cv);
      llv.push_back(cur);
      for (size_t i=0, nchildren=cur.getNumChildren(); i<nchildren; i++)
      {
        visit.push_back(cur[i]);
      }
      continue;
    }
    if (lbind.find(cv)==lbind.end())
    {
      lbind[cv] = idc;
      idc++;
    }
  }while(!visit.empty());
  for (size_t i=0, lsize = llv.size(); i<lsize; i++)
  {
    const Expr& l = llv[lsize-1-i];
    const ExprValue * lv = l.getValue();
    if (lbind.find(lv)!=lbind.end())
    {
      ll.push_back(l);
    }
  }
  return lbind;
}

void Expr::printDebugInternal(const Expr& e,
                                   std::ostream& os,
                                   std::map<const ExprValue*, size_t>& lbind)
{
  std::map<const ExprValue*, size_t>::iterator itl;
  std::vector<std::pair<Expr, size_t>> visit;
  std::pair<Expr, size_t> cur;
  visit.emplace_back(e, 0);
  do {
    cur = visit.back();
    if (cur.second==0)
    {
      itl = lbind.find(cur.first.getValue());
      if (itl!=lbind.end())
      {
        os << "_v" << itl->second;
        visit.pop_back();
        continue;
      }
      Kind k = cur.first.getKind();
      if (cur.first.getNumChildren()==0)
      {
        const Literal * l = d_state->getLiteral(cur.first.getValue());
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
        if (k!=Kind::APPLY && k!=Kind::TUPLE)
        {
          os <<  kindToTerm(k) << " ";
        }
        visit.back().second++;
        visit.emplace_back(cur.first[0], 0);
      }
    }
    else if (cur.second==cur.first.getNumChildren())
    {
      os << ")";
      visit.pop_back();
    }
    else
    {
      os << " ";
      visit.back().second++;
      visit.emplace_back(cur.first[cur.second], 0);
    }
  } while (!visit.empty());
}

void Expr::printDebug(const Expr& e, std::ostream& os)
{
  std::map<const ExprValue*, size_t> lbind;
  std::string cparen;
  if (d_state->getOptions().d_printLet)
  {
    std::vector<Expr> ll;
    lbind = computeLetBinding(e, ll);
    std::stringstream osc;
    for (const Expr& l : ll)
    {
      const ExprValue * lv = l.getValue();
      size_t id = lbind[lv];
      os << "(let ((_v" << id << " ";
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
  std::unordered_set<const ExprValue *> visited;
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
    const ExprValue * cv = cur.getValue();
    if (visited.find(cv)!=visited.end())
    {
      continue;
    }
    visited.insert(cv);
    if (cur.getKind()==Kind::PARAM)
    {
      ret.push_back(cur);
      continue;
    }
    for (size_t i=0, nchildren=cur.getNumChildren(); i<nchildren; i++)
    {
      toVisit.push_back(cur[i]);
    }
  }
  return ret;
}

size_t Expr::getNumChildren() const
{
  return d_value->getNumChildren();
}

Expr Expr::operator[](size_t i) const
{
  return Expr(d_value->d_children[i]);
}

Expr Expr::operator=(const Expr& e)
{
  d_value->dec();
  d_value = e.d_value;
  d_value->inc();
  return *this;
}

bool Expr::operator==(const Expr& e) const
{
  return d_value==e.d_value;
}
bool Expr::operator!=(const Expr& e) const
{
  return d_value!=e.d_value;
}
Kind Expr::getKind() const
{
  return d_value->getKind();
}

bool Expr::hasVariable(const Expr& e, const std::unordered_set<const ExprValue*>& vars)
{
  if (vars.empty())
  {
    return false;
  }
  std::unordered_set<const ExprValue *> visited;
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
    const ExprValue * cv = cur.getValue();
    if (visited.find(cv)!=visited.end())
    {
      continue;
    }
    visited.insert(cv);
    if (cur.getKind()==Kind::PARAM)
    {
      if (vars.find(cv)!=vars.end())
      {
        return true;
      }
    }
    for (size_t i=0, nchildren=cur.getNumChildren(); i<nchildren; i++)
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

}  // namespace alfc

