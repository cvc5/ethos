#include "state.h"

#include "error.h"

namespace atc {

State::State()
{
  ExprValue::d_state = this;
  
  bindBuiltin("lambda", Kind::LAMBDA, true);
  bindBuiltin("->", Kind::FUNCTION_TYPE, false);
}

State::~State(){}

void State::reset()
{
  d_assumptions.clear();
  d_symTable.clear();
  d_decls.clear();
  d_declsSizeCtx.clear();
}

void State::pushScope()
{
  //std::cout << "push" << std::endl;
  d_declsSizeCtx.push_back(d_decls.size());
}

void State::popScope()
{
  //std::cout << "pop" << std::endl;
  if (d_declsSizeCtx.empty())
  {
    Error::reportError("State::popScope: empty context");
  }
  size_t lastSize = d_declsSizeCtx.back();
  d_declsSizeCtx.pop_back();
  for (size_t i=lastSize, currSize = d_decls.size(); i<currSize; i++)
  {
    //std::cout << "erase " << d_decls[i] << std::endl;
    d_symTable.erase(d_decls[i]);
  }
  d_decls.resize(lastSize);
}

void State::addAssumption(const Expr& a)
{
  d_assumptions.push_back(a);
}

Expr State::mkType()
{
  return mkExprInternal(Kind::TYPE, {});
}

Expr State::mkFunctionType(const std::vector<Expr>& args, const Expr& ret)
{
  std::vector<Expr> atypes(args.begin(), args.end());
  atypes.push_back(ret);
  return mkExprInternal(Kind::FUNCTION_TYPE, atypes);
}

Expr State::mkAbstractType()
{
  return mkExprInternal(Kind::ABSTRACT_TYPE, {});
}

Expr State::mkBoolType()
{
  return mkExprInternal(Kind::BOOL_TYPE, {});
}
Expr State::mkProofType(const Expr& proven)
{
  return mkExprInternal(Kind::PROOF_TYPE, {proven});
}
Expr State::mkQuoteType(const Expr& t)
{
  return mkExprInternal(Kind::QUOTE_TYPE, {t});
}

Expr State::mkBuiltinType(Kind k)
{
  // TODO: type system for literals?
  return nullptr;
}
  
Expr State::mkVar(const std::string& name, const Expr& type)
{
  Expr v = mkExprInternal(Kind::VARIABLE, {}, false);
  // immediately set its type
  v->d_type = type;
  // map to the data
  ExprInfo* ei = getOrMkInfo(v.get());
  ei->d_str = name;
  return v;
}

Expr State::mkConst(const std::string& name, const Expr& type)
{
  // type is stored as a child
  Expr v = mkExprInternal(Kind::CONST, {}, false);
  // immediately set its type
  v->d_type = type;
  // map to the data
  ExprInfo* ei = getOrMkInfo(v.get());
  ei->d_str = name;
  return v;
}

Expr State::mkExpr(Kind k, const std::vector<Expr>& children)
{
  if (k==Kind::APPLY)
  {
    // Assert (!children.empty());
    // see if there is a special kind for the head
    ExprInfo * ei = getInfo(children[0].get());
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
  ExprInfo* ei = getOrMkInfo(lit.get());
  ei->d_str = s;
  return lit;
}

Expr State::mkExprInternal(Kind k, const std::vector<Expr>& children, bool doHash)
{
  ExprTrie* et = nullptr;
  if (doHash)
  {
    et = &d_trie[k];
    for (const Expr& e : children)
    {
      et = &(et->d_children[e]);
    }
    if (et->d_data!=nullptr)
    {
      return et->d_data;
    }
  }
  Expr ret = std::make_shared<ExprValue>(k, children);
  if (et!=nullptr)
  {
    et->d_data = ret;
  }
  return ret;
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
  std::map<const ExprValue *, ExprInfo>::const_iterator it = d_exprData.find(e.get());
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

ExprInfo* State::getInfo(const ExprValue* e)
{
  std::map<const ExprValue *, ExprInfo>::iterator it = d_exprData.find(e);
  if (it!=d_exprData.end())
  {
    return &it->second;
  }
  return nullptr;
}
  
ExprInfo* State::getOrMkInfo(const ExprValue* e)
{
  return &d_exprData[e];
}

void State::bindBuiltin(const std::string& name, Kind k, bool isClosure)
{
  // type is irrelevant, assign abstract
  bindBuiltin(name, k, isClosure, mkAbstractType());
}

void State::bindBuiltin(const std::string& name, Kind k, bool isClosure, const Expr& t)
{
  Expr c = mkConst(name, t);
  bind(name, c);
  if (isClosure || k!=Kind::NONE)
  {
    // associate the information
    ExprInfo * ei = getOrMkInfo(c.get());
    ei->d_kind = k;
    ei->d_isClosure = isClosure;
  }
}

}  // namespace atc
