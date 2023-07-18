#include "expr.h"

#include "state.h"

namespace atc {
  
State* ExprValue::d_state = nullptr;

ExprValue::ExprValue() : d_kind(Kind::NONE){}

ExprValue::ExprValue(Kind k,
      const std::vector<std::shared_ptr<ExprValue>>& children) : d_kind(k), d_children(children){}
ExprValue::~ExprValue() {}

bool ExprValue::isNull() const { return d_kind==Kind::NONE; }
  
bool ExprValue::isEqual(const std::shared_ptr<ExprValue>& val) const
{
  if (this==val.get())
  {
    return true;
  }
  if (d_kind!=val->getKind())
  {
    return false;
  }
  const std::vector<std::shared_ptr<ExprValue>>& vchildren = val->getChildren();
  if (d_children.size()!=vchildren.size())
  {
    
  }
  
  return true;
}
  
Kind ExprValue::getKind() const { return d_kind; }

const std::vector<std::shared_ptr<ExprValue>>& ExprValue::getChildren() const { return d_children; }

void ExprValue::printDebug(std::ostream& os) const
{
  // TODO
}

std::shared_ptr<ExprValue> ExprValue::getType()
{
  switch(d_kind)
  {
    case Kind::VARIABLE:
      // type is the first child
      //Assert (d_children.size()==1);
      return d_children[0];
    case Kind::APPLY:
    {
      Expr hdType = d_children[0]->getType();
      std::vector<Expr> expectedTypes;
      if (hdType->getKind()!=Kind::FUNCTION)
      {
        // non-function at head
        return nullptr;
      }
      const std::vector<Expr>& hdtypes = hdType->getChildren();
      if (hdtypes.size()!=d_children.size())
      {
        // incorrect arity
        return nullptr;
      }
      Expr retType = hdtypes.back();
      for (size_t i=1, nchild=d_children.size(); i<nchild; i++)
      {
        Expr ctype = d_children[i]->getType();
        // TODO: unification, update retType
      }
      return retType;
    }
    case Kind::LAMBDA:
    {
      std::vector<Expr> args;
      const std::vector<Expr>& vars = d_children[0]->getChildren();
      for (const Expr& c : vars)
      {
        args.push_back(c->getType());
      }
      Expr ret = d_children[1]->getType();
      return d_state->mkFunctionType(args, ret);
    }
    case Kind::TYPE:
    case Kind::FUNCTION:
    case Kind::ABSTRACT:
      return d_state->mkType();
    case Kind::INTEGER:
    case Kind::DECIMAL:
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    case Kind::STRING:
      return d_state->mkBuiltinType(d_kind);
    default:
      break;
  }
  return nullptr;
}
  
std::ostream& operator<<(std::ostream& out, const ExprValue& e)
{
  e.printDebug(out);
  return out;
}

}  // namespace atc

