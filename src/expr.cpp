#include "expr.h"

#include <unordered_map>
#include <set>
#include <iostream>
#include "state.h"
#include "error.h"

namespace atc {
  
State* ExprValue::d_state = nullptr;

ExprValue::ExprValue() : d_kind(Kind::NONE), d_flags(0) {}

ExprValue::ExprValue(Kind k,
      const std::vector<std::shared_ptr<ExprValue>>& children) : d_kind(k), d_children(children){}
ExprValue::~ExprValue() {}

bool ExprValue::isNull() const { return d_kind==Kind::NONE; }
  
bool ExprValue::isEqual(const std::shared_ptr<ExprValue>& val) const
{
  return this==val.get();
}
  
Kind ExprValue::getKind() const { return d_kind; }

const std::vector<std::shared_ptr<ExprValue>>& ExprValue::getChildren() const { return d_children; }

size_t ExprValue::getNumChildren() const
{
  return d_children.size();
}
std::shared_ptr<ExprValue> ExprValue::operator[](size_t i) const
{
  return d_children[i];
}

std::unordered_set<std::shared_ptr<ExprValue>> ExprValue::getFreeSymbols() const
{
  std::unordered_set<std::shared_ptr<ExprValue>> ret;
  // TODO
  return ret;
}

bool ExprValue::hasVariable()
{
  std::unordered_set<ExprValue*> visited;
  std::vector<ExprValue*> visit;
  visit.emplace_back(this);
  ExprValue * cur;
  do
  {
    cur = visit.back();
    if (cur->getFlag(Flag::HAS_VARIABLE_COMPUTED))
    {
      visit.pop_back();
      continue;
    }
    std::vector<Expr>& children = cur->d_children;
    if (children.empty())
    {
      cur->setFlag(Flag::HAS_VARIABLE_COMPUTED, true);
      cur->setFlag(Flag::HAS_VARIABLE, cur->getKind()==Kind::VARIABLE);
      visit.pop_back();
    }
    else if (visited.find(cur)==visited.end())
    {
      visited.insert(cur);
      for (Expr& c : children)
      {
        visit.push_back(c.get());
      }
    }
    else
    {
      visit.pop_back();
      cur->setFlag(Flag::HAS_VARIABLE_COMPUTED, true);
      for (Expr& c : children)
      {
        if (c->getFlag(Flag::HAS_VARIABLE))
        {
          cur->setFlag(Flag::HAS_VARIABLE, true);
          break;
        }
      }
    }
  }
  while (!visit.empty());
  return getFlag(Flag::HAS_VARIABLE);
}

std::string ExprValue::getSymbol() const
{
  ExprInfo * ei = d_state->getInfo(this);
  if (ei!=nullptr)
  {
    return ei->d_str;
  }
  return "";
}
  
void ExprValue::printDebug(const std::shared_ptr<ExprValue>& e, std::ostream& os)
{
  std::vector<std::pair<const ExprValue*, size_t>> visit;
  std::pair<const ExprValue*, size_t> cur;
  visit.emplace_back(e.get(), 0);
  do {
    cur = visit.back();
    if (cur.second==0)
    {
      Kind k = cur.first->getKind();
      if (cur.first->getNumChildren()==0)
      {
        ExprInfo * ei = d_state->getInfo(cur.first);
        if (ei!=nullptr)
        {
          os << ei->d_str;
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
        if (k!=Kind::APPLY)
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

std::ostream& operator<<(std::ostream& out, const Expr& e)
{
  ExprValue::printDebug(e, out);
  return out;
}

}  // namespace atc

