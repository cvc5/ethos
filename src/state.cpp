#include "state.h"

namespace atc {

State::State(){}
State::~State(){}

void State::reset()
{
  
}

void State::pushScope()
{
}
void State::popScope()
{
  
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
  return ret;
}

void State::bind(const std::string& name, const Expr& e)
{
  
}

bool State::isClosure(const std::string& name) const 
{
  return false;
}
Expr State::getVar(const std::string& name)
{
  return nullptr;
}

}  // namespace atc
