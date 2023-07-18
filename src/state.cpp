#include "state.h"

namespace atc {

State::State(){}
State::~State(){}

void State::reset()
{
  // TODO
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
    // TODO
    exit(1);
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
  return nullptr;
}

Expr State::mkFunctionType(const std::vector<Expr>& args, const Expr& ret)
{
  return nullptr;
}
  
Expr State::mkVar(const std::string& s, const Expr& type)
{
  return nullptr;
}
  
Expr State::mkExpr(Kind k, const std::vector<Expr>& children)
{
  return nullptr;
}

Expr State::mkLiteral(Kind k, const std::string& s) const
{
  return nullptr;
}

std::vector<Expr> State::mkAndBindVars(
    const std::vector<std::pair<std::string, Expr> >& sortedVarNames)
{
  std::vector<Expr> ret;
  for (const std::pair<std::string, Expr>& sv : sortedVarNames)
  {
    Expr v = mkVar(sv.first, sv.second);
    bind(sv.first, v);
    ret.push_back(v);
  }
  return ret;
}

void State::bind(const std::string& name, const Expr& e)
{
  if (d_symTable.find(name)!=d_symTable.end())
  {
    // TODO: error
  }
  d_symTable[name] = e;
  d_decls.push_back(name);
}

bool State::isClosure(const std::string& name) const 
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
