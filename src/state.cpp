#include "state.h"

#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "parser.h"
#include "util/filesystem.h"

namespace alfc {

Options::Options()
{
  d_compile = false;
  d_runCompile = false;
  d_printLet = false;
  d_stats = false;
  d_ruleSymTable = true;
  d_normalizeDecimal = true;
  d_normalizeHexadecimal = true;
}

State::State(Options& opts, Stats& stats)
    : d_hashCounter(0),
      d_hasReference(false),
      d_inGarbageCollection(false),
      d_tc(*this, opts),
      d_opts(opts),
      d_stats(stats)
{
  ExprValue::d_state = this;
  d_absType = Expr(mkExprInternal(Kind::ABSTRACT_TYPE, {}));

  // lambda is not builtin?
  // forall, exists, choice?
  //bindBuiltin("lambda", Kind::LAMBDA, true);
  bindBuiltin("->", Kind::FUNCTION_TYPE);
  bindBuiltin("_", Kind::APPLY);

  bindBuiltinEval("is_eq", Kind::EVAL_IS_EQ);
  bindBuiltinEval("ite", Kind::EVAL_IF_THEN_ELSE);
  bindBuiltinEval("requires", Kind::EVAL_REQUIRES);
  bindBuiltinEval("hash", Kind::EVAL_HASH);
  // TODO: compare?
  // lists
  bindBuiltinEval("to_list", Kind::EVAL_TO_LIST);
  bindBuiltinEval("from_list", Kind::EVAL_FROM_LIST);
  bindBuiltinEval("cons", Kind::EVAL_CONS);
  // boolean
  bindBuiltinEval("not", Kind::EVAL_NOT);
  bindBuiltinEval("and", Kind::EVAL_AND);
  bindBuiltinEval("or", Kind::EVAL_OR);
  bindBuiltinEval("xor", Kind::EVAL_XOR);
  // arithmetic
  bindBuiltinEval("add", Kind::EVAL_ADD);
  bindBuiltinEval("neg", Kind::EVAL_NEG);
  bindBuiltinEval("mul", Kind::EVAL_MUL);
  bindBuiltinEval("zdiv", Kind::EVAL_INT_DIV);
  bindBuiltinEval("zmod", Kind::EVAL_INT_MOD);
  bindBuiltinEval("qdiv", Kind::EVAL_RAT_DIV);
  bindBuiltinEval("is_neg", Kind::EVAL_IS_NEG);
  bindBuiltinEval("to_z", Kind::EVAL_TO_INT);
  bindBuiltinEval("to_q", Kind::EVAL_TO_RAT);
  bindBuiltinEval("to_bin", Kind::EVAL_TO_BV);
  bindBuiltinEval("to_str", Kind::EVAL_TO_STRING);
  // strings
  bindBuiltinEval("len", Kind::EVAL_LENGTH);
  bindBuiltinEval("concat", Kind::EVAL_CONCAT);
  bindBuiltinEval("extract", Kind::EVAL_EXTRACT);
  bindBuiltinEval("find", Kind::EVAL_FIND);

  d_nil = Expr(mkExprInternal(Kind::NIL, {}));
  bind("alf.nil", d_nil);
  // self is a distinguished parameter
  d_self = Expr(mkSymbolInternal(Kind::PARAM, "alf.self", mkAbstractType()));
  bind("alf.self", d_self);

  // note we don't allow parsing (Proof ...), (Quote ...), or (quote ...).

  // common constants
  d_type = Expr(mkExprInternal(Kind::TYPE, {}));
  d_boolType = Expr(mkExprInternal(Kind::BOOL_TYPE, {}));
  d_true = Expr(new Literal(true));
  bind("true", d_true);
  d_false = Expr(new Literal(false));
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

State::~State() {}

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
  if (d_declsSizeCtx.empty())
  {
    ALFC_FATAL() << "State::popScope: empty context";
  }
  size_t lastSize = d_declsSizeCtx.back();
  d_declsSizeCtx.pop_back();
  for (size_t i=lastSize, currSize = d_decls.size(); i<currSize; i++)
  {
    if (d_decls[i].second==0)
    {
      d_symTable.erase(d_decls[i].first);
    }
    else
    {
      // otherwise this is an overload
      AppInfo* ai = getAppInfo(d_symTable[d_decls[i].first].getValue());
      Assert (ai!=nullptr);
      ai->d_overloads.erase(d_decls[i].second-1);
    }
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
bool State::includeFile(const std::string& s)
{
  return includeFile(s, false, d_null);
}
bool State::includeFile(const std::string& s, bool isReference, const Expr& referenceNf)
{
  Filepath inputPath;
  Filepath file(s);
  if (file.isAbsolute())
  {
    inputPath = file;
  }
  else
  {
    inputPath = d_inputFile.parentPath();
    inputPath.append(file);
  }
  inputPath.makeCanonical();

  if (!inputPath.exists())
  {
    return false;
  }

  if (!markIncluded(inputPath))
  {
    return true;
  }
  Assert (!isReference || !d_hasReference);
  d_hasReference = isReference;
  d_referenceNf = referenceNf;
  Filepath currentPath = d_inputFile;
  d_inputFile = inputPath;
  if (d_compiler!=nullptr)
  {
    Assert (!isReference);
    d_compiler->includeFile(inputPath);
  }
  Trace("state") << "Include " << inputPath << std::endl;
  Assert (getAssumptionLevel()==0);
  Parser p(*this, isReference);
  p.setFileInput(inputPath.getRawPath());
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
    ALFC_FATAL() << "Including file " << inputPath.getRawPath()
                 << " did not preserve assumption scope";
  }
  return true;
}

bool State::markIncluded(const Filepath& s)
{
  std::set<Filepath>::iterator it = d_includes.find(s);
  if (it != d_includes.end())
  {
    return false;
  }
  d_includes.insert(s);
  return true;
}

void State::markDeleted(ExprValue* e)
{
  Assert(e != nullptr);
  d_stats.d_deleteExprCount++;
  if (d_inGarbageCollection)
  {
    d_toDelete.push_back(e);
    return;
  }
  d_inGarbageCollection = true;
  do
  {
    Kind k = e->getKind();
    Trace("gc") << "Delete " << e << " " << k << std::endl;
    switch(k)
    {
      case Kind::NUMERAL:
      {
        std::unordered_map<Integer, Expr, IntegerHashFunction>::iterator it = d_litIntMap.find(e->asLiteral()->d_int);
        Assert (it!=d_litIntMap.end());
        d_litIntMap.erase(it);
      }
        break;
      case Kind::DECIMAL:
      case Kind::RATIONAL:
      {
        size_t i = k==Kind::DECIMAL ? 0 : 1;
        std::unordered_map<Rational, Expr, RationalHashFunction>& m = d_litRatMap[i];
        std::unordered_map<Rational, Expr, RationalHashFunction>::iterator it = m.find(e->asLiteral()->d_rat);
        Assert (it!=m.end());
        m.erase(it);
      }
        break;
      case Kind::HEXADECIMAL:
      case Kind::BINARY:
      {
        size_t i = k==Kind::HEXADECIMAL ? 0 : 1;
        std::unordered_map<BitVector, Expr, BitVectorHashFunction>& m = d_litBvMap[i];
        std::unordered_map<BitVector, Expr, BitVectorHashFunction>::iterator it = m.find(e->asLiteral()->d_bv);
        Assert (it!=m.end());
        m.erase(it);
      }
        break;
      case Kind::STRING:
      {
        std::unordered_map<String, Expr, StringHashFunction>::iterator it = d_litStrMap.find(e->asLiteral()->d_str);
        Assert (it!=d_litStrMap.end());
        d_litStrMap.erase(it);
      }
        break;
      default:
      {
        if (isSymbol(k))
        {
          std::map<const ExprValue*, AppInfo>::const_iterator it = d_appData.find(e);
          if (it != d_appData.end())
          {
            d_appData.erase(it);
          }
        }
      }
      break;
    }
    std::map<const ExprValue*, size_t>::const_iterator ith = d_hashMap.find(e);
    if (ith != d_hashMap.end())
    {
      d_hashMap.erase(ith);
    }
    std::map<const ExprValue*, Expr>::const_iterator itt = d_typeCache.find(e);
    if (itt != d_typeCache.end())
    {
      d_typeCache.erase(itt);
    }
    // remove from the expression trie
    ExprTrie* et = &d_trie[e->getKind()];
    Assert(et != nullptr);
    const std::vector<ExprValue*>& children = e->d_children;
    et->remove(children);
    // now, free the expression
    free(e);
    if (!d_toDelete.empty())
    {
      e = d_toDelete.back();
      d_toDelete.pop_back();
    }
    else
    {
      e = nullptr;
    }
  } while (e != nullptr);
  d_inGarbageCollection = false;
}

bool State::addAssumption(const Expr& a)
{
  d_assumptions.push_back(a);
  if (d_hasReference)
  {
    // only care if at assumption level zero
    if (d_assumptionsSizeCtx.empty())
    {
      Expr aa = a;
      if (!d_referenceNf.isNull())
      {
        aa = mkExpr(Kind::APPLY, {d_referenceNf, a});
      }
      return d_referenceAsserts.find(aa.getValue()) != d_referenceAsserts.end();
    }
  }
  return true;
}

void State::addReferenceAssert(const Expr& a)
{
  Expr aa = a;
  if (!d_referenceNf.isNull())
  {
    aa = mkExpr(Kind::APPLY, {d_referenceNf, a});
  }
  d_referenceAsserts.insert(aa.getValue());
  // ensure ref count
  d_referenceAssertList.push_back(aa);
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
  return mkSymbol(Kind::CONST, name, t);
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
    std::vector<ExprValue*> atypes;
    for (size_t i = 0, nargs = args.size(); i < nargs; i++)
    {
      atypes.push_back(args[i].getValue());
    }
    atypes.push_back(ret.getValue());
    return Expr(mkExprInternal(Kind::FUNCTION_TYPE, atypes));
  }
  Expr curr = ret;
  for (size_t i=0, nargs = args.size(); i<nargs; i++)
  {
    Expr a = args[(nargs-1)-i];
    // process arguments
    if (a.getKind() == Kind::EVAL_REQUIRES)
    {
      curr = mkRequires(a[0], a[1], curr);
      a = a[2];
    }
    // append the function
    curr = Expr(
        mkExprInternal(Kind::FUNCTION_TYPE, {a.getValue(), curr.getValue()}));
  }
  return curr;
}

Expr State::mkRequires(const std::vector<Expr>& args, const Expr& ret)
{
  Expr curr = ret;
  for (size_t i=0, nargs=args.size(); i<nargs; i++)
  {
    size_t ii = (nargs-1)-i;
    Assert(args[ii].getKind() == Kind::TUPLE && args[ii].getNumChildren() == 2);
    curr = mkRequires(args[ii][0], args[ii][1], curr);
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
  return Expr(mkExprInternal(Kind::EVAL_REQUIRES,
                             {a1.getValue(), a2.getValue(), ret.getValue()}));
}

Expr State::mkAbstractType() { return d_absType; }

Expr State::mkBoolType()
{
  return d_boolType;
}
Expr State::mkProofType(const Expr& proven)
{
  return Expr(mkExprInternal(Kind::PROOF_TYPE, {proven.getValue()}));
}
Expr State::mkQuoteType(const Expr& t)
{
  return Expr(mkExprInternal(Kind::QUOTE_TYPE, {t.getValue()}));
}

Expr State::mkBuiltinType(Kind k)
{
  // for now, just use abstract type
  return d_absType;
}

Expr State::mkAnnotatedType(const Expr& t, Attr ck, const Expr& cons)
{
  if (ck!=Attr::RIGHT_ASSOC_NIL && ck!=Attr::LEFT_ASSOC_NIL)
  {
    return t;
  }
  if (cons.getKind() != Kind::NIL)
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
    Expr argAdd;
    if (curr.getKind() == Kind::FUNCTION_TYPE && curr.getNumChildren() == 2)
    {
      argAdd = curr[0];
      curr = curr[1];
    }
    else if (curr.getKind() == Kind::EVAL_REQUIRES)
    {
      currReqs.push_back(mkPair(curr[0], curr[1]));
      curr = curr[2];
    }
    else
    {
      argAdd = curr;
      curr = Expr();
    }
    if (!argAdd.isNull())
    {
      if (!currReqs.empty())
      {
        if (args.empty())
        {
          return d_null;
        }
        args.back() = mkRequires(currReqs, args.back());
        currReqs.clear();
      }
      args.push_back(argAdd);
    }
  } while (!curr.isNull() && args.size() < 3);
  if (args.size()<3)
  {
    return d_null;
  }
  Expr nilArg = args[isRight ? 1 : 0];
  std::stringstream ss;
  ss << nilArg << "_or_nil";
  Expr u = mkSymbol(Kind::PARAM, ss.str(), d_type);
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

Expr State::mkSymbol(Kind k, const std::string& name, const Expr& type)
{
  return Expr(mkSymbolInternal(k, name, type));
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
  return Expr(mkExprInternal(Kind::TUPLE, {t1.getValue(), t2.getValue()}));
}

ExprValue* State::mkSymbolInternal(Kind k,
                                   const std::string& name,
                                   const Expr& type)
{
  d_stats.d_mkExprCount++;
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
  d_stats.d_exprCount++;
  std::vector<ExprValue*> emptyVec;
  ExprValue* v = new Literal(k, name);
  // immediately set its type
  d_typeCache[v] = type;
  Trace("type_checker") << "TYPE " << name << " : " << type << std::endl;
  //d_symcMap[key] = v;
  return v;
}

Expr State::mkExpr(Kind k, const std::vector<Expr>& children)
{
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  if (k==Kind::APPLY)
  {
    Assert(!children.empty());
    // see if there is a special way of building terms for the head
    ExprValue* hd = vchildren[0];
    AppInfo* ai = getAppInfo(hd);
    if (ai!=nullptr)
    {
      if (ai->d_kind!=Kind::NONE)
      {
        if (ai->d_kind==Kind::FUNCTION_TYPE)
        {
          // functions (from parsing) are flattened here
          std::vector<Expr> achildren(children.begin()+1, children.end()-1);
          return mkFunctionType(achildren, children.back());
        }
        // another builtin operator, possibly APPLY
        std::vector<Expr> achildren(children.begin()+1, children.end());
        // must call mkExpr again, since we may auto-evaluate
        return mkExpr(ai->d_kind, achildren);
      }
      if (!ai->d_overloads.empty())
      {
        Trace("overload") << "Use overload when constructing " << k << " " << children << std::endl;
        std::map<size_t, Expr>::iterator ito = ai->d_overloads.find(children.size()-1);
        if (ito!=ai->d_overloads.end() && ito->second.getValue()!=hd)
        {
          std::vector<Expr> newChildren;
          newChildren.emplace_back(ito->second);
          newChildren.insert(newChildren.end(), children.begin()+1, children.end());
          Expr ret = mkExpr(k, newChildren);
          Trace("overload") << "...made " << ret << std::endl;
          return ret;
        }
      }
      // if it has a constructor attribute
      switch (ai->d_attrCons)
      {
        case Attr::LEFT_ASSOC:
        case Attr::RIGHT_ASSOC:
        case Attr::LEFT_ASSOC_NIL:
        case Attr::RIGHT_ASSOC_NIL:
        {
          size_t nchild = vchildren.size();
          // note that nchild>=2 treats e.g. (or a) as (or a false).
          // checking nchild>2 treats (or a) as a function Bool -> Bool.
          if (nchild>=2)
          {
            bool isLeft = (ai->d_attrCons==Attr::LEFT_ASSOC ||
                           ai->d_attrCons==Attr::LEFT_ASSOC_NIL);
            bool isNil = (ai->d_attrCons==Attr::RIGHT_ASSOC_NIL ||
                          ai->d_attrCons==Attr::LEFT_ASSOC_NIL);
            size_t i = 1;
            ExprValue* curr = vchildren[isLeft ? i : nchild - i];
            std::vector<ExprValue*> cc{hd, nullptr, nullptr};
            size_t nextIndex = isLeft ? 2 : 1;
            size_t prevIndex = isLeft ? 1 : 2;
            // note the nil element is always treated as a list
            if (curr->getKind()!=Kind::NIL && isNil)
            {
              if (getConstructorKind(curr) != Attr::LIST)
              {
                // if the last term is not marked as a list variable and
                // we have a null terminator, then we insert the null terminator
                curr = ai->d_attrConsTerm.getValue();
                i--;
              }
            }
            // now, add the remaining children
            i++;
            while (i<nchild)
            {
              cc[prevIndex] = curr;
              cc[nextIndex] = vchildren[isLeft ? i : nchild - i];
              // if the "head" child is marked as list, we construct Kind::EVAL_CONCAT
              if (isNil && getConstructorKind(cc[nextIndex]) == Attr::LIST)
              {
                curr = mkExprInternal(Kind::EVAL_CONCAT, cc);
              }
              else
              {
                curr = mkApplyInternal(cc);
              }
              i++;
            }
            return Expr(curr);
          }
          // otherwise partial??
        }
          break;
        case Attr::CHAINABLE:
        {
          std::vector<Expr> cchildren;
          Assert(!ai->d_attrConsTerm.isNull());
          cchildren.push_back(ai->d_attrConsTerm);
          std::vector<ExprValue*> cc{hd, nullptr, nullptr};
          for (size_t i=1, nchild = vchildren.size()-1; i<nchild; i++)
          {
            cc[1] = vchildren[i];
            cc[2] = vchildren[i + 1];
            cchildren.emplace_back(mkApplyInternal(cc));
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
          Assert(!ai->d_attrConsTerm.isNull());
          cchildren.push_back(ai->d_attrConsTerm);
          std::vector<ExprValue*> cc{hd, nullptr, nullptr};
          for (size_t i=1, nchild = vchildren.size(); i<nchild-1; i++)
          {
            for (size_t j=i+1; j<nchild; j++)
            {
              cc[1] = vchildren[i];
              cc[2] = vchildren[j];
              cchildren.emplace_back(mkApplyInternal(cc));
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
      const std::vector<ExprValue*>& vars = (*hd)[0]->getChildren();
      size_t nvars = vars.size();
      if (nvars==children.size()-1)
      {
        Ctx ctx;
        for (size_t i=0; i<nvars; i++)
        {
          ctx[vars[i]] = vchildren[i + 1];
        }
        Expr ret = d_tc.evaluate((*hd)[1], ctx);
        Trace("state") << "BETA_REDUCE " << Expr((*hd)[1]) << " " << ctx << " = " << ret << std::endl;
        return ret;
      }
    }
    else if (hk==Kind::PROGRAM_CONST || hk==Kind::ORACLE)
    {
      // have to check whether we have marked the constructor kind, which is
      // not the case i.e. if we are constructing applications corresponding to
      // the cases in the program definition itself.
      if (getConstructorKind(hd)!=Attr::NONE)
      {
        Expr hdt = Expr(hd);
        const Expr& t = d_tc.getType(hdt);
        // only do this if the correct arity
        if (t.getNumChildren() == children.size())
        {
          Ctx ctx;
          Expr e = d_tc.evaluateProgramInternal(vchildren, ctx);
          if (!e.isNull())
          {
            Expr ret = d_tc.evaluate(e.getValue(), ctx);
            Trace("state") << "EAGER_EVALUATE " << ret << std::endl;
            return ret;
          }
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
        return Expr(mkApplyInternal(vchildren));
      }
    }
  }
  else if (isLiteralOp(k))
  {
    // only if correct arity, else we will catch the type error
    if (TypeChecker::checkArity(k, children.size()))
    {
      // return the evaluation
      return d_tc.evaluateLiteralOp(k, vchildren);
    }
  }
  return Expr(mkExprInternal(k, vchildren));
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
  // convert string to literal
  Literal lit;
  switch (k)
  {
    case Kind::BOOLEAN:
      Assert (s=="true" || s=="false");
      return s=="true" ? d_true : d_false;
      break;
    case Kind::NUMERAL: lit = Literal(Integer(s)); break;
    case Kind::DECIMAL: lit = Literal(k, Rational::fromDecimal(s)); break;
    case Kind::RATIONAL: lit = Literal(k, Rational(s)); break;
    case Kind::HEXADECIMAL: lit = Literal(k, BitVector(s, 16)); break;
    case Kind::BINARY: lit = Literal(k, BitVector(s, 2)); break;
    case Kind::STRING: lit = Literal(String(s, true)); break;
    default:
      ALFC_FATAL() << "Unknown kind for mkLiteral " << k;
      break;
  }
  return Expr(mkLiteralInternal(lit));
}

ExprValue* State::mkLiteralInternal(Literal& l)
{
  d_stats.d_mkExprCount++;
  ExprValue * ev;
  Kind k = l.getKind();
  switch (k)
  {
    case Kind::BOOLEAN:
      return l.d_bool ? d_true.getValue() : d_false.getValue();
    case Kind::NUMERAL:
    {
      std::unordered_map<Integer, Expr, IntegerHashFunction>::iterator it = d_litIntMap.find(l.d_int);
      if (it!=d_litIntMap.end())
      {
        return it->second.getValue();
      }
      ev = new Literal(l.d_int);
      d_litIntMap[l.d_int] = Expr(ev);
    }
      break;
    case Kind::DECIMAL:
    case Kind::RATIONAL:
    {
      size_t i = k==Kind::DECIMAL ? 0 : 1;
      std::unordered_map<Rational, Expr, RationalHashFunction>& m = d_litRatMap[i];
      std::unordered_map<Rational, Expr, RationalHashFunction>::iterator it = m.find(l.d_rat);
      if (it!=m.end())
      {
        return it->second.getValue();
      }
      ev = new Literal(k, l.d_rat);
      m[l.d_rat] = Expr(ev);
    }
      break;
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    {
      size_t i = k==Kind::HEXADECIMAL ? 0 : 1;
      std::unordered_map<BitVector, Expr, BitVectorHashFunction>& m = d_litBvMap[i];
      std::unordered_map<BitVector, Expr, BitVectorHashFunction>::iterator it = m.find(l.d_bv);
      if (it!=m.end())
      {
        return it->second.getValue();
      }
      ev = new Literal(k, l.d_bv);
      m[l.d_bv] = Expr(ev);
    }
      break;
    case Kind::STRING:
    {
      std::unordered_map<String, Expr, StringHashFunction>::iterator it = d_litStrMap.find(l.d_str);
      if (it!=d_litStrMap.end())
      {
        return it->second.getValue();
      }
      ev = new Literal(l.d_str);
      d_litStrMap[l.d_str] = Expr(ev);
    }
      break;
    default:
      ALFC_FATAL() << "Unknown kind for mkLiteralInternal " << l.getKind();
      break;
  }
  d_stats.d_litCount++;
  d_stats.d_exprCount++;
  return ev;
}

ExprValue* State::mkApplyInternal(const std::vector<ExprValue*>& children)
{
  Assert(children.size() > 2);
  // requires currying
  ExprValue* curr = children[0];
  for (size_t i=1, nchildren = children.size(); i<nchildren; i++)
  {
    curr = mkExprInternal(Kind::APPLY, {curr, children[i]});
  }
  return curr;
}

ExprValue* State::mkExprInternal(Kind k,
                                 const std::vector<ExprValue*>& children)
{
  d_stats.d_mkExprCount++;
  ExprTrie* et = &d_trie[k];
  et = et->get(children);
  if (et->d_data!=nullptr)
  {
    return et->d_data;
  }
  d_stats.d_exprCount++;
  ExprValue* ev = new ExprValue(k, children);
  Trace("gc") << "New " << ev << " " << k << std::endl;
  et->d_data = ev;
  return ev;
}

bool State::bind(const std::string& name, const Expr& e)
{
  // compiler is agnostic to which symbol table, record it here
  if (d_compiler!=nullptr)
  {
    d_compiler->bind(name, e);
  }
  // if using a separate symbol table for rules
  if (d_opts.d_ruleSymTable && e.getKind() == Kind::PROOF_RULE)
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
  std::map<std::string, Expr>::iterator its = d_symTable.find(name);
  if (its!=d_symTable.end())
  {
    // try to overload?
    AppInfo& ai = d_appData[its->second.getValue()];
    Expr ee = e;
    Expr et = d_tc.getType(ee);
    size_t arity = 0;
    while (et.getKind()==Kind::FUNCTION_TYPE)
    {
      arity++;
      et = et[et.getNumChildren()-1];
      while (et.getKind()==Kind::EVAL_REQUIRES)
      {
        et = et[2];
      }
    }
    Trace("overload") << "Overload " << e << " for " << its->second << " with arity " << arity << std::endl;
    if (ai.d_overloads.find(arity)!=ai.d_overloads.end())
    {
      return false;
    }
    ai.d_overloads[arity] = e;
    if (!d_declsSizeCtx.empty())
    {
      d_decls.emplace_back(name, arity+1);
    }
    return true;
  }
  // Trace("state-debug") << "bind " << name << " -> " << &e << std::endl;
  d_symTable[name] = e;
  // only have to remember if not at global scope
  if (!d_declsSizeCtx.empty())
  {
    d_decls.emplace_back(name, 0);
  }
  return true;
}

bool State::isClosure(const ExprValue* e) const
{
  return getConstructorKind(e) == Attr::CLOSURE;
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
  return d_null;
}

Expr State::getProofRule(const std::string& name) const
{
  const std::map<std::string, Expr>& t = d_opts.d_ruleSymTable ? d_ruleSymTable : d_symTable;
  std::map<std::string, Expr>::const_iterator it = t.find(name);
  if (it!=t.end())
  {
    return it->second;
  }
  return d_null;
}

bool State::matchesConclusion(const ExprValue* rule)
{
  AppInfo* ainfo = getAppInfo(rule);
  return (ainfo != nullptr
          && (ainfo->d_attrCons == Attr::MATCH_CONCLUSION
              || ainfo->d_attrCons == Attr::PREMISE_LIST_MATCH_CONCLUSION));
}

bool State::getActualPremises(const ExprValue* rule,
                              std::vector<Expr>& given,
                              std::vector<Expr>& actual)
{
  AppInfo* ainfo = getAppInfo(rule);
  if (ainfo != nullptr
      && (ainfo->d_attrCons == Attr::PREMISE_LIST
          || ainfo->d_attrCons == Attr::PREMISE_LIST_MATCH_CONCLUSION))
  {
    Expr plCons = ainfo->d_attrConsTerm;
    if (!plCons.isNull())
    {
      std::vector<Expr> achildren;
      achildren.push_back(plCons);
      for (Expr& e : given)
      {
        // should be proof types
        Expr eproven = d_tc.getType(e);
        if (eproven.isNull() || eproven.getKind() != Kind::PROOF_TYPE)
        {
          return false;
        }
        achildren.push_back(eproven[0]);
      }
      Expr ap = mkExpr(Kind::APPLY, achildren);
      Expr pfap = mkProofType(ap);
      // TODO: collect operator???
      // dummy, const term of the given proof type
      Expr n = mkSymbol(Kind::CONST, "tmp", pfap);
      actual.push_back(n);
      return true;
    }
  }
  actual = given;
  return true;
}

Expr State::getProgram(const ExprValue* ev)
{
  AppInfo* ainfo = getAppInfo(ev);
  if (ainfo!=nullptr && ainfo->d_attrCons==Attr::PROGRAM)
  {
    return ainfo->d_attrConsTerm;
  }
  return d_null;
}
bool State::getOracleCmd(const ExprValue* oracle, std::string& ocmd)
{
  AppInfo* ainfo = getAppInfo(oracle);
  if (ainfo!=nullptr && ainfo->d_attrCons==Attr::ORACLE)
  {
    Expr oexpr = ainfo->d_attrConsTerm;
    Assert(!oexpr.isNull());
    ocmd = oexpr.getSymbol();
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

bool State::hasReference() const
{
  return d_hasReference;
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

ExprValue* State::lookupType(const ExprValue* e) const
{
  std::map<const ExprValue*, Expr>::const_iterator itt = d_typeCache.find(e);
  if (itt != d_typeCache.end())
  {
    return itt->second.getValue();
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
  bindBuiltin(name, k, ac, d_absType);
}

void State::bindBuiltin(const std::string& name, Kind k, Attr ac, const Expr& t)
{
  Expr c = mkSymbol(Kind::CONST, name, t);
  bind(name, c);
  if (ac!=Attr::NONE || k!=Kind::NONE)
  {
    // associate the information
    AppInfo& ai = d_appData[c.getValue()];
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
  markConstructorKind(v, Attr::PROGRAM, prog);
  if (d_compiler!=nullptr)
  {
    d_compiler->defineProgram(v, prog);
  }
}

bool State::markConstructorKind(const Expr& v, Attr a, const Expr& cons)
{
  Expr acons = cons;
  if (a==Attr::ORACLE)
  {
    // use full path
    std::string ocmd = cons.getSymbol();

    Filepath inputPath = d_inputFile.parentPath();
    inputPath.append(Filepath(ocmd));
    inputPath.makeCanonical();

    if (!inputPath.exists())
    {
      Warning() << "State:: could not include \"" + ocmd + "\" for oracle definition";
      return false;
    }

    acons = mkLiteral(Kind::STRING, inputPath.getRawPath());
  }
  Assert (isSymbol(v.getKind()));
  AppInfo& ai = d_appData[v.getValue()];
  Assert (ai.d_attrCons==Attr::NONE);
  ai.d_attrCons = a;
  ai.d_attrConsTerm = acons;
  if (d_compiler!=nullptr)
  {
    d_compiler->markConstructorKind(v, a, acons);
  }
  return true;
}

}  // namespace alfc
