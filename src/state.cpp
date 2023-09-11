#include "state.h"

#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "parser.h"

namespace alfc {

Options::Options()
{
  d_compile = false;
  d_runCompile = false;
  d_printLet = false;
  d_stats = false;
  d_ruleSymTable = true;
}

State::State(Options& opts, Stats& stats) : d_hashCounter(0), d_hasReference(false), d_tc(*this), d_opts(opts), d_stats(stats)
{
  ExprValue::d_state = this;
  
  // lambda is not builtin?
  //bindBuiltin("lambda", Kind::LAMBDA, true);
  bindBuiltin("->", Kind::FUNCTION_TYPE);
  bindBuiltin("_", Kind::APPLY);

  bindBuiltinEval("is_eq", Kind::EVAL_IS_EQ);
  bindBuiltinEval("ite", Kind::EVAL_IF_THEN_ELSE);
  bindBuiltinEval("requires", Kind::EVAL_REQUIRES);
  bindBuiltinEval("hash", Kind::EVAL_HASH);
  // lists
  bindBuiltinEval("to_list", Kind::EVAL_TO_LIST);
  bindBuiltinEval("from_list", Kind::EVAL_FROM_LIST);
  bindBuiltinEval("cons", Kind::EVAL_CONS);
  bindBuiltinEval("append", Kind::EVAL_APPEND);
  // boolean
  bindBuiltinEval("not", Kind::EVAL_NOT);
  bindBuiltinEval("and", Kind::EVAL_AND);
  bindBuiltinEval("or", Kind::EVAL_OR);
  // arithmetic
  bindBuiltinEval("add", Kind::EVAL_ADD);
  bindBuiltinEval("neg", Kind::EVAL_NEG);
  bindBuiltinEval("mul", Kind::EVAL_MUL);
  bindBuiltinEval("zdiv", Kind::EVAL_INT_DIV);
  bindBuiltinEval("qdiv", Kind::EVAL_RAT_DIV);
  bindBuiltinEval("is_neg", Kind::EVAL_IS_NEG);
  bindBuiltinEval("is_zero", Kind::EVAL_IS_ZERO);
  bindBuiltinEval("to_z", Kind::EVAL_TO_INT);
  bindBuiltinEval("to_q", Kind::EVAL_TO_RAT);
  bindBuiltinEval("to_bin", Kind::EVAL_TO_BV);
  bindBuiltinEval("to_str", Kind::EVAL_TO_STRING);
  // strings
  bindBuiltinEval("len", Kind::EVAL_LENGTH);
  bindBuiltinEval("concat", Kind::EVAL_CONCAT);
  bindBuiltinEval("extract", Kind::EVAL_EXTRACT);
  
  d_nil = mkExprInternal(Kind::NIL, {});
  bind("alf.nil", d_nil);
  d_fail = mkExprInternal(Kind::FAIL, {});
  bind("alf.fail", d_fail);
  // self is a distinguished parameter
  d_self = mkSymbolInternal(Kind::PARAM, "alf.self", mkAbstractType());
  bind("alf.self", d_self);

  // note we don't allow parsing (Proof ...), (Quote ...), or (quote ...).

  // common constants
  d_type = mkExprInternal(Kind::TYPE, {});
  d_boolType = mkExprInternal(Kind::BOOL_TYPE, {});
  d_true = mkLiteral(Kind::BOOLEAN, "true");
  bind("true", d_true);
  d_false = mkLiteral(Kind::BOOLEAN, "false");
  bind("false", d_false);
  if (d_opts.d_runCompile)
  {
    Assert(!d_opts.d_compile);
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
  d_symTable.clear();
  d_assumptions.clear();
  d_assumptionsSizeCtx.clear();
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
    ALFC_FATAL() << "State::popScope: empty context";
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

void State::pushAssumptionScope()
{
  if (d_compiler!=nullptr)
  {
    d_compiler->popScope();
  }
  d_assumptionsSizeCtx.push_back(d_assumptions.size());
}

void State::popAssumptionScope()
{
  if (d_compiler!=nullptr)
  {
    d_compiler->popScope();
  }
  // process assumptions
  size_t lastSize = d_assumptionsSizeCtx.back();
  d_assumptionsSizeCtx.pop_back();
  d_assumptions.resize(lastSize);
}

void State::includeFile(const std::string& s, bool isReference)
{
  std::filesystem::path inputPath;
  try {
    inputPath = std::filesystem::canonical(d_inputFile.parent_path() / s);
  }
  catch (std::filesystem::filesystem_error const&)
  {
    ALFC_FATAL() << "State::includeFile: could not include \"" + s + "\"";
  }
  if (!markIncluded(inputPath))
  {
    return;
  }
  std::filesystem::path currentPath = d_inputFile;
  d_inputFile = inputPath;
  if (d_compiler!=nullptr)
  {
    d_compiler->includeFile(inputPath);
  }
  Trace("state") << "Include " << inputPath << std::endl;
  Assert (getAssumptionLevel()==0);
  Parser p(*this, isReference);
  p.setFileInput(inputPath);
  bool parsedCommand;
  do
  {
    parsedCommand = p.parseNextCommand();
  }
  while (parsedCommand);
  d_inputFile = currentPath;
  Trace("state") << "...finished" << std::endl;
  if (getAssumptionLevel()!=0)
  {
    ALFC_FATAL() << "Including file " << inputPath << " did not preserve assumption scope";
  }
}

bool State::markIncluded(const std::string& s)
{
  std::set<std::filesystem::path>::iterator it = d_includes.find(s);
  if (it!=d_includes.end())
  {
    return false;
  }
  d_includes.insert(s);
  return true;
}

void State::markDeleted(const ExprValue * e)
{
  std::map<const ExprValue *, AppInfo>::const_iterator it = d_appData.find(e);
  if (it!=d_appData.end())
  {
    d_appData.erase(it);
  }
  std::map<const ExprValue*, Literal>::const_iterator itl = d_literals.find(e);
  if (itl!=d_literals.end())
  {
    d_literals.erase(itl);
  }
  std::map<const ExprValue*, size_t>::const_iterator ith = d_hashMap.find(e);
  if (ith!=d_hashMap.end())
  {
    d_hashMap.erase(ith);
  }
}

bool State::addAssumption(const Expr& a)
{
  d_assumptions.push_back(a);
  if (d_hasReference)
  {
    // only care if at assumption level zero
    if (d_assumptionsSizeCtx.empty())
    {
      return d_referenceAsserts.find(a)!=d_referenceAsserts.end();
    }
  }
  return true;
}

void State::addReferenceAssert(const Expr& a)
{
  d_referenceAsserts.insert(a);
}

void State::setLiteralTypeRule(Kind k, const Expr& t)
{
  d_tc.setLiteralTypeRule(k, t);
  if (d_compiler!=nullptr)
  {
    d_compiler->setLiteralTypeRule(k, t);
  }
}

Expr State::mkType()
{
  return d_type;
}

Expr State::mkTypeConstant(const std::string& name, size_t arity)
{
  Expr t;
  if (arity == 0)
  {
    t = d_type;
  }
  else
  {
    std::vector<Expr> args;
    for (size_t i=0; i<arity; i++)
    {
      args.push_back(d_type);
    }
    t = mkFunctionType(args, d_type);
  }
  return mkConst(name, t);
}

Expr State::mkFunctionType(const std::vector<Expr>& args, const Expr& ret, bool flatten)
{
  if (args.empty())
  {
    return ret;
  }
  // process restrictions
  if (!flatten)
  {
    std::vector<Expr> atypes(args.begin(), args.end());
    atypes.push_back(ret);
    return mkExprInternal(Kind::FUNCTION_TYPE, atypes);
  }
  Expr curr = ret;
  for (size_t i=0, nargs = args.size(); i<nargs; i++)
  {
    Expr a = args[(nargs-1)-i];
    // process arguments
    if (a->getKind()==Kind::EVAL_REQUIRES)
    {
      curr = mkRequires(a->d_children[0], a->d_children[1], curr);
      a = a->d_children[2];
    }
    // append the function
    curr = mkExprInternal(Kind::FUNCTION_TYPE, {a, curr});
  }
  return curr;
}

Expr State::mkRequires(const std::vector<Expr>& args, const Expr& ret)
{
  Expr curr = ret;
  for (size_t i=0, nargs=args.size(); i<nargs; i++)
  {
    size_t ii = (nargs-1)-i;
    Assert (args[ii]->getKind()==Kind::TUPLE && args[ii]->getNumChildren()==2);
    curr = mkRequires((*args[ii].get())[0], (*args[ii].get())[1], curr);
  }
  return curr;
}

Expr State::mkRequires(const Expr& a1, const Expr& a2, const Expr& ret)
{
  if (a1==a2)
  {
    // trivially equal to return
    return ret;
  }
  return mkExprInternal(Kind::EVAL_REQUIRES, {a1, a2, ret});
}

Expr State::mkAbstractType()
{
  return mkExprInternal(Kind::ABSTRACT_TYPE, {});
}

Expr State::mkBoolType()
{
  return d_boolType;
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

Expr State::mkAnnotatedType(const Expr& t, Attr ck, const Expr& cons)
{
  if (ck!=Attr::RIGHT_ASSOC_NIL && ck!=Attr::LEFT_ASSOC_NIL)
  {
    return t;
  }
  if (cons->getKind()!=Kind::NIL)
  {
    return t;
  }
  bool isRight = (ck==Attr::RIGHT_ASSOC_NIL);
  std::vector<Expr> args;
  // decompose into (-> t1 t2 t3)
  Expr curr = t;
  std::vector<Expr> currReqs;
  do
  {
    Expr argAdd = nullptr;
    std::vector<Expr>& children = curr->getChildren();
    if (curr->getKind()==Kind::FUNCTION_TYPE && children.size()==2)
    {
      argAdd = children[0];
      curr = children[1];
    }
    else if (curr->getKind()==Kind::EVAL_REQUIRES)
    {
      currReqs.push_back(mkPair(children[0], children[1]));
      curr = children[2];
    }
    else
    {
      argAdd = curr;
      curr = nullptr;
    }
    if (argAdd!=nullptr)
    {
      if (!currReqs.empty())
      {
        if (args.empty())
        {
          return nullptr;
        }
        args.back() = mkRequires(currReqs, args.back());
        currReqs.clear();
      }
      args.push_back(argAdd);
    }
  }
  while (curr!=nullptr && args.size()<3);
  if (args.size()<3)
  {
    return nullptr;
  }
  Expr nilArg = args[isRight ? 1 : 0];
  std::stringstream ss;
  ss << nilArg << "_or_nil";
  Expr u = mkParameter(ss.str(), d_type);
  Expr cond = mkExpr(Kind::EVAL_IS_EQ, {u, d_nil});
  if (isRight)
  {
    // (-> t1 (-> t2 t3)) :right-assoc-nil
    //   is
    // (-> t1 (-> U (alf.ite (alf.is_eq U alf.nil) t3 (Requires U t2 t3))))
    Expr ret = args[2];
    ret = mkExpr(Kind::EVAL_IF_THEN_ELSE, {
                cond, ret, mkRequires(u, nilArg, ret)});
    return mkFunctionType({args[0], u}, ret);
  }
  else
  {
    // (-> t1 (-> t2 t3)) :left-assoc-nil
    //   is
    // (-> U (alf.ite (alf.is_eq U alf.nil) (-> t2 t3) (Requires U t1 (-> t2 t3))))
    Expr ret = mkFunctionType({args[1]}, args[2]);
    ret = mkExpr(Kind::EVAL_IF_THEN_ELSE, {
                  cond, ret, mkRequires(u, nilArg, ret)});
    return mkFunctionType({u}, ret);
  }

  return t;
}

Expr State::mkParameter(const std::string& name, const Expr& type)
{
  return mkSymbolInternal(Kind::PARAM, name, type);
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

Expr State::mkOracle(const std::string& name, const Expr& type)
{
  return mkSymbolInternal(Kind::ORACLE, name, type);
}

Expr State::mkSelf()
{
  return d_self;
}

Expr State::mkNil()
{
  return d_nil;
}

Expr State::mkPair(const Expr& t1, const Expr& t2)
{
  return mkExprInternal(Kind::TUPLE, {t1, t2});
}

Expr State::mkSymbolInternal(Kind k, const std::string& name, const Expr& type)
{
  // TODO: symbols can be shared if no attributes
  /*
  std::tuple<Kind, std::string, Expr> key(k, name, type);  
  std::map<std::tuple<Kind, std::string, Expr>, Expr>::iterator it = d_symcMap.find(key);
  if (it!=d_symcMap.end())
  {
    return it->second;
  }
  */
  d_stats.d_symCount++;
  std::vector<Expr> emptyVec;
  Expr v = std::make_shared<ExprValue>(k, emptyVec);
  // immediately set its type
  v->d_type = type;
  // map to the data
  d_literals[v.get()] = Literal(name);
  Trace("type_checker") << "TYPE " << name << " : " << type << std::endl;
  //d_symcMap[key] = v;
  return v;
}

Expr State::mkExpr(Kind k, const std::vector<Expr>& children)
{
  if (k==Kind::APPLY)
  {
    Assert(!children.empty());
    // see if there is a special way of building terms for the head
    const Expr& hd = children[0];
    AppInfo * ai = getAppInfo(hd.get());
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
        // must call mkExpr again, since we may auto-evaluate
        return mkExpr(ai->d_kind, achildren);
      }
      // if it has a constructor attribute
      switch (ai->d_attrCons)
      {
        case Attr::LEFT_ASSOC:
        case Attr::RIGHT_ASSOC:
        case Attr::LEFT_ASSOC_NIL:
        case Attr::RIGHT_ASSOC_NIL:
        {
          size_t nchild = children.size();
          // note that nchild>=2 treats e.g. (or a) as (or a false).
          // checking nchild>2 treats (or a) as a function Bool -> Bool.
          if (nchild>=2)
          {
            bool isLeft = (ai->d_attrCons==Attr::LEFT_ASSOC ||
                           ai->d_attrCons==Attr::LEFT_ASSOC_NIL);
            bool isNil = (ai->d_attrCons==Attr::RIGHT_ASSOC_NIL ||
                          ai->d_attrCons==Attr::LEFT_ASSOC_NIL);
            size_t i = 1;
            Expr curr = children[isLeft ? i : nchild-i];
            std::vector<Expr> cc{hd, nullptr, nullptr};
            size_t nextIndex = isLeft ? 2 : 1;
            size_t prevIndex = isLeft ? 1 : 2;
            // note the nil element is always treated as a list
            if (curr->getKind()!=Kind::NIL && isNil)
            {
              if (getConstructorKind(curr.get())!=Attr::LIST)
              {
                // if the last term is not marked as a list variable and
                // we have a null terminator, then we insert the null terminator
                curr = ai->d_attrConsTerm;
                i--;
              }
            }
            // now, add the remaining children
            i++;
            while (i<nchild)
            {
              cc[prevIndex] = curr;
              cc[nextIndex] = children[isLeft ? i : nchild-i];
              // if the "head" child is marked as list, we construct Kind::EVAL_APPEND
              if (getConstructorKind(cc[nextIndex].get())==Attr::LIST)
              {
                curr = mkExprInternal(Kind::EVAL_APPEND, cc);
              }
              else
              {
                curr = mkApplyInternal(cc);
              }
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
          Assert(ai->d_attrConsTerm != nullptr);
          cchildren.push_back(ai->d_attrConsTerm);
          std::vector<Expr> cc{hd, nullptr, nullptr};
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
          std::vector<Expr> cchildren;
          Assert(ai->d_attrConsTerm != nullptr);
          cchildren.push_back(ai->d_attrConsTerm);
          std::vector<Expr> cc{hd, nullptr, nullptr};
          for (size_t i=1, nchild = children.size(); i<nchild-1; i++)
          {
            for (size_t j=i+1; j<nchild; j++)
            {
              cc[1] = children[i];
              cc[2] = children[j];
              cchildren.push_back(mkApplyInternal(cc));
            }
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
        default:
          break;
      }
    }
    Kind hk = hd->getKind();
    if (hk==Kind::LAMBDA)
    {
      // beta-reduce eagerly, if the correct arity
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
        Trace("state") << "BETA_REDUCE " << body << " " << ctx << " = " << ret << std::endl;
        return ret;
      }
    }
    else if (hk==Kind::PROGRAM_CONST)
    {
      // if all arguments are ground, just evaluate immediately
      bool allGround = true;
      for (size_t i=1, nchild = children.size(); i<nchild; i++)
      {
        if (!children[i]->isGround())
        {
          allGround = false;
          break;
        }
      }
      // have to check whether we have the program, i.e. if we are constructing
      // applications corresponding to the cases in the program definition itself.
      if (allGround && d_tc.hasProgram(hd))
      {
        Expr hdt = hd;
        const Expr& t = d_tc.getType(hdt);
        // only do this if the correct arity
        if (t->getNumChildren()==children.size())
        {
          Ctx ctx;
          Expr e = d_tc.evaluateProgram(children, ctx);
          Expr ret = d_tc.evaluate(e, ctx);
          Trace("state") << "EAGER_EVALUATE " << ret << std::endl;
          return ret;
        }
      }
    }
    // Most functions are unary and require currying if applied to more than one argument.
    // The exceptions to this are operators whose types are not flattened (programs and proof rules).
    if (children.size()>2)
    {
      if (hk!=Kind::PROGRAM_CONST && hk!=Kind::PROOF_RULE && hk!=Kind::ORACLE)
      {
        // return the curried version
        return mkApplyInternal(children);
      }
    }
  }
  else if (isLiteralOp(k))
  {
    // only if correct arity, else we will catch the type error
    if (TypeChecker::checkArity(k, children.size()))
    {
      // if all arguments are ground, just evaluate immediately
      bool allGround = true;
      for (size_t i=0, nchild = children.size(); i<nchild; i++)
      {
        if (!children[i]->isGround())
        {
          allGround = false;
          break;
        }
      }
      if (allGround)
      {
        Expr ret = d_tc.evaluateLiteralOp(k, children);
        // return if successfully evaluated
        if (ret!=nullptr)
        {
          Trace("state") << "EAGER_EVALUATE " << ret << std::endl;
          return ret;
        }
      }
    }
  }
  return mkExprInternal(k, children);
}

Expr State::mkTrue()
{
  return d_true;
}

Expr State::mkFalse()
{
  return d_false;
}

Expr State::mkLiteral(Kind k, const std::string& s)
{
  std::pair<Kind, std::string> key(k, s);
  std::map<std::pair<Kind, std::string>, Expr>::iterator it = d_literalTrie.find(key);
  if (it!=d_literalTrie.end())
  {
    return it->second;
  }
  d_stats.d_litCount++;
  std::vector<Expr> emptyVec;
  Expr lit = std::make_shared<ExprValue>(k, emptyVec);
  // map to the data
  d_literalTrie[key] = lit;
  //std::cout << "mkLiteral \"" << s << "\"" << std::endl;
  // convert string to literal
  switch (k)
  {
    case Kind::BOOLEAN:
      Assert (s=="true" || s=="false");
      d_literals[lit.get()] = Literal(s=="true");
      break;
    case Kind::NUMERAL:
      d_literals[lit.get()] = Literal(Integer(s));
      break;
    case Kind::DECIMAL:
      d_literals[lit.get()] = Literal(Rational(s));
      break;
    case Kind::HEXADECIMAL:
      // TODO: should normalize to binary?
      break;
    case Kind::BINARY:
      d_literals[lit.get()] = Literal(BitVector(s, 2));
      break;
    case Kind::STRING:
      d_literals[lit.get()] = Literal(String(s, true));
      break;
    default:
      break;
  }
  return lit;
}

Expr State::mkLiteralNumeral(size_t val)
{
  // TODO: optimize
  std::stringstream ss;
  ss << val;
  return mkLiteral(Kind::NUMERAL, ss.str());
}

Expr State::mkApplyInternal(const std::vector<Expr>& children)
{
  Assert(children.size() > 2);
  // requires currying
  Expr curr = children[0];
  for (size_t i=1, nchildren = children.size(); i<nchildren; i++)
  {
    curr = mkExprInternal(Kind::APPLY, {curr, children[i]});
  }
  return curr;
}

Expr State::mkExprInternal(Kind k, const std::vector<Expr>& children)
{
  d_stats.d_mkExprCount++;
  ExprTrie* et = &d_trie[k];
  for (const Expr& e : children)
  {
    et = &(et->d_children[e.get()]);
  }
  if (et->d_data!=nullptr)
  {
    return et->d_data;
  }
  d_stats.d_exprCount++;
  Expr ret = std::make_shared<ExprValue>(k, children);
  et->d_data = ret;
  return ret;
}

bool State::bind(const std::string& name, const Expr& e)
{
  // compiler is agnostic to which symbol table, record it here
  if (d_compiler!=nullptr)
  {
    d_compiler->bind(name, e);
  }
  // if using a separate symbol table for rules
  if (d_opts.d_ruleSymTable && e->getKind()==Kind::PROOF_RULE)
  {
    // don't bind at non-global scope
    Assert (d_declsSizeCtx.empty());
    if (d_ruleSymTable.find(name)!=d_ruleSymTable.end())
    {
      return false;
    }
    d_ruleSymTable[name] = e;
    return true;
  }
  // otherwise use the main symbol table
  if (d_symTable.find(name)!=d_symTable.end())
  {
    return false;
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
  return getConstructorKind(e.get())==Attr::CLOSURE;
}

Attr State::getConstructorKind(const ExprValue* v) const
{
  std::map<const ExprValue *, AppInfo>::const_iterator it = d_appData.find(v);
  if (it!=d_appData.end())
  {
    return it->second.d_attrCons;
  }
  return Attr::NONE;
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

Expr State::getProofRule(const std::string& name) const
{
  const std::map<std::string, Expr>& t = d_opts.d_ruleSymTable ? d_ruleSymTable : d_symTable;
  std::map<std::string, Expr>::const_iterator it = t.find(name);
  if (it!=t.end())
  {
    return it->second;
  }
  return nullptr;
}

Literal* State::getLiteral(const ExprValue* e)
{
  std::map<const ExprValue *, Literal>::iterator it = d_literals.find(e);
  if (it!=d_literals.end())
  {
    return &it->second;
  }
  return nullptr;
}

bool State::getActualPremises(const Expr& rule, std::vector<Expr>& given, std::vector<Expr>& actual)
{
  AppInfo* ainfo = getAppInfo(rule.get());
  if (ainfo!=nullptr && ainfo->d_attrCons==Attr::PREMISE_LIST)
  {
    Expr plCons = ainfo->d_attrConsTerm;
    if (plCons!=nullptr)
    {
      std::vector<Expr> achildren;
      achildren.push_back(plCons);
      for (Expr& e : given)
      {
        // should be proof types
        Expr eproven = d_tc.getType(e);
        if (eproven==nullptr || eproven->getKind()!=Kind::PROOF_TYPE)
        {
          return false;
        }
        achildren.push_back((*eproven.get())[0]);
      }
      Expr ap;
      if (achildren.size()==2)
      {
        ap = achildren[1];
      }
      else
      {
        ap = mkExpr(Kind::APPLY, achildren);
      }
      Expr pfap = mkProofType(ap);
      // TODO: collect operator???
      // dummy, const term of the given proof type
      Expr n = mkConst("tmp", pfap);
      actual.push_back(n);
      return true;
    }
  }
  actual = given;
  return true;
}
bool State::getOracleCmd(const Expr& oracle, std::string& ocmd)
{
  AppInfo* ainfo = getAppInfo(oracle.get());
  if (ainfo!=nullptr && ainfo->d_attrCons==Attr::ORACLE)
  {
    Expr oexpr = ainfo->d_attrConsTerm;
    Assert (oexpr!=nullptr);
    ocmd = oexpr->getSymbol();
    return true;
  }
  return false;
}

size_t State::getAssumptionLevel() const
{
  return d_assumptionsSizeCtx.size();
}

std::vector<Expr> State::getCurrentAssumptions() const
{
  size_t start = d_assumptionsSizeCtx.empty() ? 0 : d_assumptionsSizeCtx.back();
  std::vector<Expr> as(d_assumptions.begin()+start, d_assumptions.end());
  return as;
}

size_t State::getHash(const ExprValue* e)
{
  std::map<const ExprValue*, size_t>::const_iterator it = d_hashMap.find(e);
  if (it!=d_hashMap.end())
  {
    return it->second;
  }
  d_hashCounter++;
  size_t ret = d_hashCounter;
  d_hashMap[e] = ret;
  return ret;
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

Stats& State::getStats()
{
  return d_stats;
}

Compiler* State::getCompiler()
{
  return d_compiler.get();
}

void State::bindBuiltin(const std::string& name, Kind k, Attr ac)
{
  // type is irrelevant, assign abstract
  bindBuiltin(name, k, ac, mkAbstractType());
}

void State::bindBuiltin(const std::string& name, Kind k, Attr ac, const Expr& t)
{
  Expr c = mkConst(name, t);
  bind(name, c);
  if (ac!=Attr::NONE || k!=Kind::NONE)
  {
    // associate the information
    AppInfo& ai = d_appData[c.get()];
    ai.d_kind = k;
    ai.d_attrCons = ac;
  }
}

void State::bindBuiltinEval(const std::string& name, Kind k, Attr ac)
{
  bindBuiltin("alf."+name, k, ac);
}

void State::defineProgram(const Expr& v, const Expr& prog)
{
  d_tc.defineProgram(v, prog);
  if (d_compiler!=nullptr)
  {
    d_compiler->defineProgram(v, prog);
  }
}

void State::markConstructorKind(const Expr& v, Attr a, const Expr& cons)
{
  Expr acons = cons;
  if (a==Attr::ORACLE)
  {
    // use full path
    std::string ocmd = cons->getSymbol();
    std::filesystem::path inputPath;
    try {
      inputPath = std::filesystem::canonical(d_inputFile.parent_path() / ocmd);
    }
    catch (std::filesystem::filesystem_error const&)
    {
      ALFC_FATAL() << "State:: could not include \"" + ocmd + "\" for oracle definition";
    }
    acons = mkLiteral(Kind::STRING, inputPath);
  }
  AppInfo& ai = d_appData[v.get()];
  Assert (ai.d_attrCons==Attr::NONE);
  ai.d_attrCons = a;
  ai.d_attrConsTerm = acons;
  if (d_compiler!=nullptr)
  {
    d_compiler->markConstructorKind(v, a, acons);
  }
}
void State::markHasReference()
{
  d_hasReference = true;
}

}  // namespace alfc
