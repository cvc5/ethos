#include "state.h"

#include "error.h"

namespace atc {

State::State()
{
  ExprValue::d_state = this;
  
  bindBuiltin("lambda", Kind::LAMBDA, true);
  bindBuiltin("->", Kind::FUNCTION, false);
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
  return mkExprInternal(Kind::TYPE, {});
}

Expr State::mkFunctionType(const std::vector<Expr>& args, const Expr& ret)
{
  std::vector<Expr> atypes(args.begin(), args.end());
  atypes.push_back(ret);
  return mkExprInternal(Kind::FUNCTION, atypes);
}

Expr State::mkAbstractType()
{
  return nullptr;
}

Expr State::mkBuiltinType(Kind k)
{
  return nullptr;
}
  
Expr State::mkVar(const std::string& name, const Expr& type)
{
  // type is stored as a child
  Expr v = mkExprInternal(Kind::VARIABLE, {type});
  // map to the data
  ExprInfo* ei = getOrMkInfo(v);
  ei->d_str = name;
  return v;
}

Expr State::mkConst(const std::string& name, const Expr& type)
{
  // type is stored as a child
  Expr v = mkExprInternal(Kind::CONST, {type});
  // map to the data
  ExprInfo* ei = getOrMkInfo(v);
  ei->d_str = name;
  return v;
}

Expr State::mkExpr(Kind k, const std::vector<Expr>& children)
{
  if (k==Kind::APPLY)
  {
    // Assert (!children.empty());
    // see if there is a special kind for the head
    ExprInfo * ei = getInfo(children[0]);
    if (ei!=nullptr && ei->d_kind!=Kind::NONE)
    {
      std::vector<Expr> achildren(children.begin()+1, children.end());
      return mkExprInternal(ei->d_kind, achildren);
    }
  }
  return mkExprInternal(k, children);
}

Expr State::mkLiteral(Kind k, const std::string& s)
{
  Expr lit = mkExprInternal(k, {});
  // map to the data
  ExprInfo* ei = getOrMkInfo(lit);
  ei->d_str = s;
  return lit;
}

Expr State::mkExprInternal(Kind k, const std::vector<Expr>& children)
{
  return std::make_shared<ExprValue>(k, children);
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
  std::map<Expr, ExprInfo>::const_iterator it = d_exprData.find(e);
  if (it!=d_exprData.end())
  {
    return it->second.d_isClosure;
  }
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

ExprInfo* State::getInfo(const Expr& e)
{
  std::map<Expr, ExprInfo>::iterator it = d_exprData.find(e);
  if (it!=d_exprData.end())
  {
    return &it->second;
  }
  return nullptr;
}
  
ExprInfo* State::getOrMkInfo(const Expr& e)
{
  return &d_exprData[e];
}

void State::bindBuiltin(const std::string& name, Kind k, bool isClosure)
{
  // type is irrelevant, assign abstract
  Expr c = mkConst(name, mkAbstractType());
  bind(name, c);
  // associate the information
  ExprInfo * ei = getOrMkInfo(c);
  ei->d_kind = k;
  ei->d_isClosure = isClosure;
}

}  // namespace atc
