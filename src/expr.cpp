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

bool ExprValue::match(std::shared_ptr<ExprValue>& val, Ctx& ctx)
{
  std::set<std::pair<ExprValue*, ExprValue*>> visited;
  std::set<std::pair<ExprValue*, ExprValue*>>::iterator it;
  std::map<ExprValue*, ExprValue*>::iterator ctxIt;

  std::vector<std::pair<ExprValue*, ExprValue*>> stack;
  stack.emplace_back(this, val.get());
  std::pair<ExprValue*, ExprValue*> curr;

  while (!stack.empty())
  {
    curr = stack.back();
    stack.pop_back();
    if (curr.first == curr.second)
    {
      // holds trivially
      continue;
    }
    it = visited.find(curr);
    if (it != visited.end())
    {
      // already processed
      continue;
    }
    visited.insert(curr);
    if (curr.first->getNumChildren() == 0)
    {
      // if the two subterms are not equal and the first one is a bound
      // variable...
      if (curr.first->getKind() == Kind::VARIABLE)
      {
        // and we have not seen this variable before...
        ctxIt = ctx.find(curr.first);
        if (ctxIt == ctx.cend())
        {
          // TODO: ensure types are the same?
          // add the two subterms to `sub`
          ctx.emplace(curr.first, curr.second);
        }
        else
        {
          // if we saw this variable before, make sure that (now and before) it
          // maps to the same subterm
          stack.emplace_back(ctxIt->second, curr.second);
        }
      }
      else
      {
        // the two subterms are not equal
        return false;
      }
    }
    else
    {
      // if the two subterms are not equal, make sure that their operators are
      // equal
      if (curr.first->getNumChildren() != curr.second->getNumChildren()
          || curr.first->getKind() != curr.second->getKind())
      {
        return false;
      }
      // recurse on children
      for (size_t i = 0, n = curr.first->getNumChildren(); i < n; ++i)
      {
        stack.emplace_back((*curr.first)[i].get(), (*curr.second)[i].get());
      }
    }
  }
  return true;
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

std::shared_ptr<ExprValue> ExprValue::getType(std::ostream& out)
{
  if (d_type==nullptr)
  {
    d_type = getTypeInternal(out);
  }
  return d_type;
}

std::shared_ptr<ExprValue> ExprValue::getTypeInternal(std::ostream& out)
{
  switch(d_kind)
  {
    case Kind::APPLY:
    {
      Expr hdType = d_children[0]->getType(out);
      if (hdType==nullptr)
      {
        return hdType;
      }
      std::vector<Expr> expectedTypes;
      if (hdType->getKind()!=Kind::FUNCTION)
      {
        // non-function at head
        out << "Non-function as head of APPLY";
        return nullptr;
      }
      const std::vector<Expr>& hdtypes = hdType->getChildren();
      if (hdtypes.size()!=d_children.size())
      {
        // incorrect arity
        out << "Incorrect arity";
        return nullptr;
      }
      Expr retType = hdtypes.back();
      Ctx ctx;
      for (size_t i=1, nchild=d_children.size(); i<nchild; i++)
      {
        Expr ctype = d_children[i]->getType(out);
        if (ctype==nullptr)
        {
          return ctype;
        }
        // unification, update retType
        if (!hdtypes[i-1]->match(ctype, ctx))
        {
          out << "Unexpected argument type " << i << std::endl;
          out << "  LHS " << hdtypes[i-1] << std::endl;
          out << "  RHS " << ctype << std::endl;
          return nullptr;
        }
      }
      if (ctx.empty())
      {
        return retType;
      }
      return retType->clone(ctx);
    }
    case Kind::LAMBDA:
    {
      std::vector<Expr> args;
      const std::vector<Expr>& vars = d_children[0]->getChildren();
      for (const Expr& c : vars)
      {
        Expr ctype = c->getType(out);
        if (ctype==nullptr)
        {
          return ctype;
        }
        args.push_back(ctype);
      }
      Expr ret = d_children[1]->getType(out);
      if (ret==nullptr)
      {
        return ret;
      }
      return d_state->mkFunctionType(args, ret);
    }
    case Kind::TYPE:
    case Kind::ABSTRACT:
      return d_state->mkType();
    case Kind::FUNCTION:
      // the children must be types
      for (const Expr& c : d_children)
      {
        Expr ctype = c->getType(out);
        if (ctype==nullptr)
        {
          return ctype;
        }
        if (ctype->getKind()!=Kind::TYPE)
        {
          out << "Non-type for function";
          return nullptr;
        }
      }
      return d_state->mkType();
    case Kind::VARIABLE_LIST:
    case Kind::INTEGER:
    case Kind::DECIMAL:
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    case Kind::STRING:
      return d_state->mkBuiltinType(d_kind);
    default:
      break;
  }
  out << "Unknown kind " << d_kind;
  return nullptr;
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
        // if we encounter nullptr here, then this child is currently being
        // traversed at a higher level, hence this corresponds to a cyclic
        // proof.
        /*
        if (it->second == nullptr)
        {
          Unreachable() << "Cyclic expression encountered when cloning";
        }
        */
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
          os << "[" << cur.first->getKind() << "]";
        }
        visit.pop_back();
      }
      else
      {
        os << "(";
        if (k!=Kind::APPLY)
        {
          os << k;
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

