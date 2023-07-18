#include "state.h"

#include "error.h"

namespace atc {

State::State(){
  ExprValue::d_state = this;
}
State::~State(){}

void State::reset()
{
  d_symTable.clear();
  d_decls.clear();
  d_declsSizeCtx.clear();
}

void State::pushScope()
{
  d_declsSizeCtx.push_back(d_decls.size());
}

void State::popScope()
{
  if (d_declsSizeCtx.empty())
  {
    Error::reportError("State::popScope: empty context");
  }
  size_t lastSize = d_declsSizeCtx.back();
  d_declsSizeCtx.pop_back();
  for (size_t i=lastSize, currSize = d_decls.size(); i<currSize; i++)
  {
    d_symTable.erase(d_decls[i]);
  }
  d_decls.resize(lastSize);
}

Expr State::mkType()
{
  return mkExpr(Kind::TYPE, {});
}

Expr State::mkFunctionType(const std::vector<Expr>& args, const Expr& ret)
{
  std::vector<Expr> atypes(args.begin(), args.end());
  atypes.push_back(ret);
  return mkExpr(Kind::FUNCTION, atypes);
}

Expr State::mkAbstractType()
{
  return nullptr;
}

Expr State::mkBuiltinType(Kind k)
{
  return nullptr;
}
  
Expr State::mkVar(const std::string& s, const Expr& type)
{
  // type is stored as a child
  return mkExpr(Kind::VARIABLE, {type});
}
  
Expr State::mkExpr(Kind k, const std::vector<Expr>& children)
{
  return std::make_shared<ExprValue>(k, children);
}

Expr State::mkLiteral(Kind k, const std::string& s)
{
  // map to data
  Expr lit = mkExpr(k, {});
  d_litData[lit] = s;
  return lit;
}

bool State::mkAndBindVars(
    const std::vector<std::pair<std::string, Expr> >& sortedVarNames, std::vector<Expr>& ret)
{
  for (const std::pair<std::string, Expr>& sv : sortedVarNames)
  {
    Expr v = mkVar(sv.first, sv.second);
    if (!bind(sv.first, v))
    {
      return false;
    }
    ret.push_back(v);
  }
  return true;
}

bool State::bind(const std::string& name, const Expr& e)
{
  if (d_symTable.find(name)!=d_symTable.end())
  {
    return false;
  }
  d_symTable[name] = e;
  d_decls.push_back(name);
  return true;
}

bool State::isClosure(const Expr& e) const 
{
  return false;
}

Expr State::getVar(const std::string& name) const
{
  std::map<std::string, Expr>::const_iterator it = d_symTable.find(name);
  if (it!=d_symTable.end())
  {
    return it->second;
  }
  return nullptr;
}

}  // namespace atc
