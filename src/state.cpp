#include "state.h"

#include "error.h"
#include "parser.h"

namespace alfc {

State::State(Options& opts) : d_tc(*this), d_opts(opts)
{
  ExprValue::d_state = this;
  
  bindBuiltin("lambda", Kind::LAMBDA, true);
  bindBuiltin("->", Kind::FUNCTION_TYPE, false);
  bindBuiltin("@", Kind::APPLY, false);
  // note we don't allow parsing (Proof ...), (Quote ...), or (quote ...).

  if (d_opts.d_runCompile)
  {
    // Assert (!d_opts.d_compile);
    run_initialize();
  }
  else if (d_opts.d_compile)
  {
    d_compiler.reset(new Compiler(*this));
  }
}

State::~State(){}

void State::reset()
{
  d_assumptions.clear();
  d_symTable.clear();
  d_decls.clear();
  d_declsSizeCtx.clear();
  if (d_compiler!=nullptr)
  {
    d_compiler->reset();
  }
}

void State::pushScope()
{
  //std::cout << "push" << std::endl;
  d_declsSizeCtx.push_back(d_decls.size());
  if (d_compiler!=nullptr)
  {
    d_compiler->pushScope();
  }
}

void State::popScope()
{
  if (d_compiler!=nullptr)
  {
    d_compiler->popScope();
  }
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

void State::includeFile(const std::string& s)
{
  includeFileInternal(s, false);
}

void State::includeFileInternal(const std::string& s, bool ignore)
{
  std::filesystem::path inputPath;
  try {
    inputPath = std::filesystem::canonical(d_inputFile.parent_path() / s);
  }
  catch (std::filesystem::filesystem_error const&)
  {
    Error::reportError("State::includeFile: could not include \"" + s + "\"");
  }
  std::set<std::filesystem::path>::iterator it = d_includes.find(inputPath);
  if (it!=d_includes.end())
  {
    return;
  }
  d_includes.insert(inputPath);
  d_inputFile = inputPath;
  if (d_compiler!=nullptr)
  {
    d_compiler->includeFile(s);
  }
  std::cout << "Include " << inputPath << std::endl;
  if (ignore)
  {
    return;
  }
  Parser p(*this);
  p.setFileInput(inputPath);
  bool parsedCommand;
  do
  {
    parsedCommand = p.parseNextCommand();
  }
  while (parsedCommand);
  std::cout << "...finished" << std::endl;
}

void State::addAssumption(const Expr& a)
{
  d_assumptions.push_back(a);
  if (d_compiler!=nullptr)
  {
    d_compiler->addAssumption(a);
  }
}

Expr State::mkType()
{
  return mkExprInternal(Kind::TYPE, {});
}

Expr State::mkFunctionType(const std::vector<Expr>& args, const Expr& ret, bool flatten)
{
  if (flatten && args.size()>1)
  {
    Expr curr = ret;
    for (size_t i=0, nargs = args.size(); i<nargs; i++)
    {
      Expr arg = args[nargs-i-1];
      curr = mkExprInternal(Kind::FUNCTION_TYPE, {arg, curr});
    }
    return curr;
  }
  std::vector<Expr> atypes(args.begin(), args.end());
  atypes.push_back(ret);
  return mkExprInternal(Kind::FUNCTION_TYPE, atypes);
}

Expr State::mkRequiresType(const std::vector<Expr>& args, const Expr& ret)
{
  std::vector<Expr> atypes(args.begin(), args.end());
  atypes.push_back(ret);
  return mkExprInternal(Kind::REQUIRES_TYPE, atypes);
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
  // for now, just use abstract type
  return mkAbstractType();
}
  
Expr State::mkVar(const std::string& name, const Expr& type)
{
  return mkSymbolInternal(Kind::VARIABLE, name, type);
}

Expr State::mkConst(const std::string& name, const Expr& type)
{
  return mkSymbolInternal(Kind::CONST, name, type);
}

Expr State::mkProgramConst(const std::string& name, const Expr& type)
{
  return mkSymbolInternal(Kind::PROGRAM_CONST, name, type);
}

Expr State::mkProofRule(const std::string& name, const Expr& type)
{
  return mkSymbolInternal(Kind::PROOF_RULE, name, type);
}

Expr State::mkSymbolInternal(Kind k, const std::string& name, const Expr& type)
{
  // type is stored as a child
  Expr v = mkExprInternal(k, {}, false);
  // immediately set its type
  if (type->isGround() && type->isEvaluatable())
  {
    // evaluate the type
    Expr t = type;
    v->d_type = d_tc.evaluate(t);
  }
  else
  {
    v->d_type = type;
  }
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
    // see if there is a special way of building terms for the head
    const Expr& hd = children[0];
    AppInfo * ai = children.empty() ? nullptr : getAppInfo(hd.get());
    if (ai!=nullptr)
    {
      if (ai->d_kind==Kind::FUNCTION_TYPE)
      {
        // functions (from parsing) are flattened here
        std::vector<Expr> achildren(children.begin()+1, children.end()-1);
        return mkFunctionType(achildren, children.back());
      }
      else if (ai->d_kind!=Kind::NONE)
      {
        // another builtin operator, possibly APPLY
        std::vector<Expr> achildren(children.begin()+1, children.end());
        return mkExprInternal(ai->d_kind, achildren);
      }
      // if it has a constructor attribute
      switch (ai->d_attrCons)
      {
        case Attr::LEFT_ASSOC:
        case Attr::RIGHT_ASSOC:
        {
          size_t nchild = children.size();
          if (nchild>2)
          {
            bool isLeft = (ai->d_attrCons==Attr::LEFT_ASSOC);
            size_t i = 1;
            Expr curr = children[isLeft ? i : nchild-i];
            std::vector<Expr> cc{hd, nullptr, nullptr};
            size_t nextIndex = isLeft ? 2 : 1;
            size_t prevIndex = isLeft ? 1 : 2;
            if (ai->d_attrConsTerm!=nullptr)
            {
              AppInfo * ail = getAppInfo(curr.get());
              if (ail==nullptr || !ail->hasAttribute(Attr::LIST))
              {
                // if the last term is not marked as a list variable and
                // we have a null terminator, then we insert the null terminator
                cc[prevIndex] = ai->d_attrConsTerm;
                cc[nextIndex] = curr;
                curr = mkApplyInternal(cc);
              }
            }
            // now, add the remaining children
            i++;
            while (i<nchild)
            {
              cc[prevIndex] = curr;
              cc[nextIndex] = children[isLeft ? i : nchild-i];
              curr = mkApplyInternal(cc);
              i++;
            }
            return curr;
          }
          // otherwise partial??
        }
          break;
        case Attr::CHAINABLE:
        {
          std::vector<Expr> cchildren;
          //Assert (ai->d_attrConsTerm!=nullptr)
          cchildren.push_back(ai->d_attrConsTerm);
          std::vector<Expr> cc{children[0], nullptr, nullptr};
          for (size_t i=1, nchild = children.size()-1; i<nchild; i++)
          {
            cc[1] = children[i];
            cc[2] = children[i+1];
            cchildren.push_back(mkApplyInternal(cc));
          }
          if (cchildren.size()==2)
          {
            // no need to chain
            return cchildren[1];
          }
          // note this could loop
          return mkExpr(Kind::APPLY, cchildren);
        }
          break;
        case Attr::PAIRWISE:
        {
          // TODO: pairwise construction
        }
          break;
        default:
          break;
      }
    }
    Kind hk = hd->getKind();
    if (hk==Kind::LAMBDA)
    {
      // beta-reduce eagerly, if the right arity
      std::vector<Expr>& vars = (*hd.get())[0]->d_children;
      size_t nvars = vars.size();
      if (nvars==children.size()-1)
      {
        Ctx ctx;
        for (size_t i=0; i<nvars; i++)
        {
          ctx[vars[i]] = children[i+1];
        }
        Expr body = (*hd.get())[1];
        Expr ret = d_tc.evaluate(body, ctx);
        //std::cout << "BETA_REDUCE " << body << " -> " << ret << std::endl;
        return ret;
      }
    }
    // all functions of kind CONST or VARIABLE are unary and require
    // currying if applied to more than one argument.
    if (children.size()>2)
    {
      if (hk==Kind::CONST || hk==Kind::VARIABLE)
      {
        // return the curried version
        return mkApplyInternal(children);
      }
    }
  }
  return mkExprInternal(k, children);
}

Expr State::mkLiteral(Kind k, const std::string& s)
{
  std::pair<Kind, std::string> key(k, s);
  std::map<std::pair<Kind, std::string>, Expr>::iterator it = d_literalTrie.find(key);
  if (it!=d_literalTrie.end())
  {
    return it->second;
  }
  Expr lit = mkExprInternal(k, {}, false);
  // map to the data
  ExprInfo* ei = getOrMkInfo(lit.get());
  ei->d_str = s;
  d_literalTrie[key] = lit;
  return lit;
}

Expr State::mkApplyInternal(const std::vector<Expr>& children)
{
  // Assert(children.size()>2);
  // requires currying
  Expr curr = children[0];
  for (size_t i=1, nchildren = children.size(); i<nchildren; i++)
  {
    curr = mkExprInternal(Kind::APPLY, {curr, children[i]}, true);
  }
  return curr;
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
  if (d_compiler!=nullptr)
  {
    d_compiler->bind(name, e);
  }
  d_symTable[name] = e;
  // only have to remember if not at global scope
  if (!d_declsSizeCtx.empty())
  {
    d_decls.push_back(name);
  }
  return true;
}

bool State::isClosure(const Expr& e) const 
{
  std::map<const ExprValue *, AppInfo>::const_iterator it = d_appData.find(e.get());
  if (it!=d_appData.end())
  {
    return it->second.hasAttribute(Attr::CLOSURE);
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

AppInfo* State::getAppInfo(const ExprValue* e)
{
  std::map<const ExprValue *, AppInfo>::iterator it = d_appData.find(e);
  if (it!=d_appData.end())
  {
    return &it->second;
  }
  return nullptr;
}

TypeChecker& State::getTypeChecker()
{
  return d_tc;
}

Options& State::getOptions()
{
  return d_opts;
}

Compiler* State::getCompiler()
{
  return d_compiler.get();
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
    AppInfo& ai = d_appData[c.get()];
    ai.d_kind = k;
    if (isClosure)
    {
      ai.d_attrs.insert(Attr::CLOSURE);
    }
  }
}

void State::defineProgram(const Expr& v, const Expr& prog)
{
  d_programs[v] = prog;
  if (d_compiler!=nullptr)
  {
    d_compiler->defineProgram(v, prog);
  }
}

Expr State::evaluate(const std::vector<Expr>& children, Ctx& newCtx)
{
  Expr hd = children[0];
  std::map<Expr, Expr>::iterator it = d_programs.find(hd);
  Expr app = mkExprInternal(Kind::APPLY, children);
  if (it==d_programs.end())
  {
    return app;
  }
  std::cout << "RUN " << app << " on " << it->second << std::endl;
  // otherwise, evaluate
  std::vector<Expr>& progChildren = it->second->getChildren();
  for (Expr& c : progChildren)
  {
    newCtx.clear();
    Expr hd = c->getChildren()[0];
    if (d_tc.match(hd, app, newCtx))
    {
      std::cout << "...matches " << hd << ", ctx size = " << newCtx.size() << std::endl;
      return c->getChildren()[1];
    }
  }
  return app;
}

bool State::markAttributes(const Expr& v, const std::map<Attr, Expr>& attrs)
{
  AppInfo& ai = d_appData[v.get()];
  for (const std::pair<const Attr, Expr>& a : attrs)
  {
    switch(a.first)
    {
      case Attr::LEFT_ASSOC:
      case Attr::RIGHT_ASSOC:
      case Attr::CHAINABLE:
        // it specifies how to construct this
        ai.d_attrCons = a.first;
        ai.d_attrConsTerm = a.second;
        // TODO: ensure its type has the right shape here?
        // would catch errors earlier
        break;
      case Attr::LIST:
        // remember it has been marked
        ai.d_attrs.insert(a.first);
        break;
      default:
        break;
    }
  }
  return true;
}

}  // namespace alfc
