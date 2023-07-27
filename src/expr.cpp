#include "expr.h"

#include <set>
#include <iostream>
#include "state.h"
#include "error.h"

namespace alfc {
  
State* ExprValue::d_state = nullptr;

ExprValue::ExprValue() : d_kind(Kind::NONE), d_flags(0) {}

ExprValue::ExprValue(Kind k,
      const std::vector<std::shared_ptr<ExprValue>>& children) : d_kind(k), d_children(children), d_flags(0){}
ExprValue::~ExprValue() {}

bool ExprValue::isNull() const { return d_kind==Kind::NONE; }
  
bool ExprValue::isEqual(const std::shared_ptr<ExprValue>& val) const
{
  return this==val.get();
}
  
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
    std::vector<Expr>& children = cur->d_children;
    if (children.empty())
    {
      bool isVar = (cur->getKind()==Kind::VARIABLE);
      cur->setFlag(Flag::IS_EVAL, false);
      cur->setFlag(Flag::IS_NON_GROUND, isVar);
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
      Kind ck = cur->getKind();
      if (ck==Kind::APPLY && children[0]->getKind()==Kind::PROGRAM_CONST)
      {
        cur->setFlag(Flag::IS_EVAL, true);
      }
      else if (ck==Kind::REQUIRES_TYPE)
      {
        // requires type may evaluate
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
      }
    }
  }
  while (!visit.empty());
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

std::ostream& operator<<(std::ostream& out, const Expr& e)
{
  ExprValue::printDebug(e, out);
  return out;
}

}  // namespace alfc

