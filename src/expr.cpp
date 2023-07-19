#include "expr.h"

#include <unordered_map>
#include <set>
#include <iostream>
#include "state.h"
#include "error.h"

namespace atc {
  
State* ExprValue::d_state = nullptr;

ExprValue::ExprValue() : d_kind(Kind::NONE){}

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

std::shared_ptr<ExprValue> ExprValue::clone(Ctx& ctx) const
{
  std::unordered_map<const ExprValue*, std::shared_ptr<ExprValue>> visited;
  std::unordered_map<const ExprValue*, std::shared_ptr<ExprValue>>::iterator it;
  std::vector<const ExprValue*> visit;
  std::shared_ptr<ExprValue> cloned;
  visit.push_back(this);
  const ExprValue* cur;
  while (!visit.empty())
  {
    cur = visit.back();
    it = visited.find(cur);
    // constants stay the same
    if (it == visited.end())
    {
      visited[cur] = nullptr;
      const std::vector<std::shared_ptr<ExprValue>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ExprValue>& cp : children)
      {
        visit.push_back(cp.get());
      }
      continue;
    }
    visit.pop_back();
    if (it->second.get() == nullptr)
    {
      std::vector<std::shared_ptr<ExprValue>> cchildren;
      const std::vector<std::shared_ptr<ExprValue>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ExprValue>& cp : children)
      {
        it = visited.find(cp.get());
        //Assert(it != visited.end());
        cchildren.push_back(it->second);
      }
      cloned = d_state->mkExpr(cur->getKind(), cchildren);
      // remember its type
      cloned->d_type = cur->d_type;
      visited[cur] = cloned;
    }
  }
  //Assert(visited.find(this) != visited.end());
  return visited[this];
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

