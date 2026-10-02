/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "state.h"

#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "util/filesystem.h"

namespace ethos {

Options::Options()
{
  d_parseLet = true;
  d_printDag = true;
  d_stats = false;
  d_statsAll = false;
  d_statsCompact = false;
  d_ruleSymTable = true;
  d_requireProofOfFalse = false;
  d_normalizeDecimal = true;
  d_normalizeHexadecimal = true;
  d_normalizeNumeral = false;
  d_referenceDefineFun = false;
}

bool Options::setOption(const std::string& key, bool val)
{
  if (key == "parse-let")
  {
    d_parseLet = val;
  }
  else if (key == "print-dag")
  {
    d_printDag = val;
  }
  else if (key == "stats")
  {
    d_stats = val;
  }
  else if (key == "stats-all")
  {
    // also implies stats are enabled.
    d_stats = val ? true : d_stats;
    d_statsAll = val;
  }
  else if (key == "stats-compact")
  {
    // also implies stats are enabled.
    d_stats = val ? true : d_stats;
    d_statsCompact = val;
  }
  else if (key == "rule-sym-table")
  {
    d_ruleSymTable = val;
  }
  else if (key == "require-proof-of-false")
  {
    d_requireProofOfFalse = val;
  }
  else if (key == "normalize-dec")
  {
    d_normalizeDecimal = val;
  }
  else if (key == "normalize-num")
  {
    d_normalizeNumeral = val;
  }
  else if (key == "normalize-hex")
  {
    d_normalizeHexadecimal = val;
  }
  else if (key == "reference-define-fun")
  {
    d_referenceDefineFun = val;
  }
  else
  {
    return false;
  }
  Trace("options") << "setOption(\"" << key << "\", " << val << ")"
                   << std::endl;
  return true;
}

State::State(Options& opts, Stats& stats)
    : d_hashCounter(0),
      d_hasReference(false),
      d_inGarbageCollection(false),
      d_lastStepProvesFalseAtLevelZero(false),
      d_opts(opts),
      d_stats(stats),
      d_tc(*this, opts),
      d_plugin(nullptr),
      d_fileReader(nullptr)
{
  ExprValue::d_state = this;

  // lambda is not builtin?
  // forall, exists, choice?
  //bindBuiltin("lambda", Kind::LAMBDA, true);
  bindBuiltin("->", Kind::FUNCTION_TYPE);
  bindBuiltin("_", Kind::APPLY);

  bindBuiltinEval("is_ok", Kind::EVAL_IS_OK);
  bindBuiltinEval("is_eq", Kind::EVAL_IS_EQ);
  bindBuiltinEval("eq", Kind::EVAL_EQ);
  bindBuiltinEval("ite", Kind::EVAL_IF_THEN_ELSE);
  bindBuiltinEval("requires", Kind::EVAL_REQUIRES);
  bindBuiltinEval("hash", Kind::EVAL_HASH);
  bindBuiltinEval("nameof", Kind::EVAL_NAME_OF);
  bindBuiltinEval("typeof", Kind::EVAL_TYPE_OF);
  bindBuiltinEval("var", Kind::VARIABLE);
  bindBuiltinEval("cmp", Kind::EVAL_COMPARE);
  bindBuiltinEval("log", Kind::EVAL_LOG);
  bindBuiltinEval("is_z", Kind::EVAL_IS_Z);
  bindBuiltinEval("is_q", Kind::EVAL_IS_Q);
  bindBuiltinEval("is_bin", Kind::EVAL_IS_BIN);
  bindBuiltinEval("is_str", Kind::EVAL_IS_STR);
  bindBuiltinEval("is_bool", Kind::EVAL_IS_BOOL);
  bindBuiltinEval("is_var", Kind::EVAL_IS_VAR);
  // lists
  bindBuiltinEval("nil", Kind::EVAL_NIL);
  bindBuiltinEval("cons", Kind::EVAL_CONS);
  bindBuiltinEval("list_len", Kind::EVAL_LIST_LENGTH);
  bindBuiltinEval("list_concat", Kind::EVAL_LIST_CONCAT);
  bindBuiltinEval("list_nth", Kind::EVAL_LIST_NTH);
  bindBuiltinEval("list_find", Kind::EVAL_LIST_FIND);
  bindBuiltinEval("list_erase", Kind::EVAL_LIST_ERASE);
  bindBuiltinEval("list_erase_all", Kind::EVAL_LIST_ERASE_ALL);
  bindBuiltinEval("list_rev", Kind::EVAL_LIST_REV);
  bindBuiltinEval("list_setof", Kind::EVAL_LIST_SETOF);
  bindBuiltinEval("list_minclude", Kind::EVAL_LIST_MINCLUDE);
  bindBuiltinEval("list_meq", Kind::EVAL_LIST_MEQ);
  bindBuiltinEval("list_diff", Kind::EVAL_LIST_DIFF);
  bindBuiltinEval("list_inter", Kind::EVAL_LIST_INTER);
  bindBuiltinEval("list_singleton_elim", Kind::EVAL_LIST_SINGLETON_ELIM);
  bindBuiltinEval("list_singleton_intro", Kind::EVAL_LIST_SINGLETON_INTRO);
  bindBuiltinEval("list_repeat", Kind::EVAL_LIST_REPEAT);
  // boolean
  bindBuiltinEval("not", Kind::EVAL_NOT);
  bindBuiltinEval("and", Kind::EVAL_AND);
  bindBuiltinEval("or", Kind::EVAL_OR);
  bindBuiltinEval("xor", Kind::EVAL_XOR);
  // arithmetic
  bindBuiltinEval("add", Kind::EVAL_ADD);
  bindBuiltinEval("neg", Kind::EVAL_NEG);
  bindBuiltinEval("mul", Kind::EVAL_MUL);
  bindBuiltinEval("pow", Kind::EVAL_POW);
  bindBuiltinEval("zdiv", Kind::EVAL_INT_DIV);
  bindBuiltinEval("zmod", Kind::EVAL_INT_MOD);
  bindBuiltinEval("qdiv", Kind::EVAL_RAT_DIV);
  bindBuiltinEval("is_neg", Kind::EVAL_IS_NEG);
  bindBuiltinEval("to_z", Kind::EVAL_TO_INT);
  bindBuiltinEval("to_q", Kind::EVAL_TO_RAT);
  bindBuiltinEval("to_bin", Kind::EVAL_TO_BIN);
  bindBuiltinEval("to_str", Kind::EVAL_TO_STRING);
  bindBuiltinEval("gt", Kind::EVAL_GT);
  // strings
  bindBuiltinEval("len", Kind::EVAL_LENGTH);
  bindBuiltinEval("concat", Kind::EVAL_CONCAT);
  bindBuiltinEval("extract", Kind::EVAL_EXTRACT);
  bindBuiltinEval("find", Kind::EVAL_FIND);
  // datatypes
  bindBuiltinEval("dt_constructors", Kind::EVAL_DT_CONSTRUCTORS);
  bindBuiltinEval("dt_selectors", Kind::EVAL_DT_SELECTORS);

  // as
  bindBuiltin("as", Kind::AS_RETURN);
  bindBuiltinEval("as", Kind::AS);

  // note we don't allow parsing (Proof ...), (Quote ...), or (quote ...).

  // common constants
  d_type = Expr(mkExprInternal(Kind::TYPE, {}));
  d_boolType = Expr(mkExprInternal(Kind::BOOL_TYPE, {}));
  d_true = Expr(new Literal(true));
  bind("true", d_true);
  d_false = Expr(new Literal(false));
  bind("false", d_false);

  // builtin lists
  d_listType = Expr(mkSymbolInternal(Kind::CONST, "eo::List", d_type));
  bind("eo::List", d_listType);
  d_listNil = Expr(mkSymbolInternal(Kind::CONST, "eo::List::nil", d_listType));
  bind("eo::List::nil", d_listNil);
  Expr t = Expr(mkSymbolInternal(Kind::PARAM, "T", d_type));
  std::vector<Expr> argTypes;
  argTypes.push_back(t);
  argTypes.push_back(d_listType);
  Expr consType = mkFunctionType(argTypes, d_listType);
  d_listCons = Expr(mkSymbolInternal(Kind::CONST, "eo::List::cons", consType));
  bind("eo::List::cons", d_listCons);
  // This impacts how eo::List::cons is parsed and how list operators, e.g.
  // eo::list_len, are evaluated on it. Note that mkList does not rely on it.
  markConstructorKind(d_listCons, Attr::RIGHT_ASSOC_NIL, d_listNil);

  // any is used internally but is not avaiable to the user
  d_any = Expr(mkExpr(Kind::ANY, {}));
  // self is a distinguished parameter
  d_self = Expr(mkSymbolInternal(Kind::PARAM, "eo::self", d_any));
  // Proof is the return type of terms with kind Kind::PROOF, which is an
  // ordinary type (not available in the parser).
  d_proofType = Expr(mkSymbolInternal(Kind::CONST, "eo::Proof", d_type));
}

State::~State() {}

void State::reset()
{
  d_symTable.clear();
  d_assumptions.clear();
  d_assumptionsSizeCtx.clear();
  d_decls.clear();
  d_declsSizeCtx.clear();
  d_lastStepProvesFalseAtLevelZero = false;
  if (d_plugin!=nullptr)
  {
    d_plugin->reset();
  }
}

void State::pushScope()
{
  d_declsSizeCtx.push_back(d_decls.size());
  if (d_plugin!=nullptr)
  {
    d_plugin->pushScope();
  }
}

void State::popScope()
{
  if (d_plugin!=nullptr)
  {
    d_plugin->popScope();
  }
  if (d_declsSizeCtx.empty())
  {
    EO_FATAL() << "State::popScope: empty context";
  }
  size_t lastSize = d_declsSizeCtx.back();
  d_declsSizeCtx.pop_back();
  size_t i = d_decls.size();
  while (i > lastSize)
  {
    i--;
    std::map<std::string, std::vector<Expr>>::iterator its =
        d_symTable.find(d_decls[i]);
    Assert(its != d_symTable.end() && !its->second.empty());
    // revert to the previous binding, if one exists
    its->second.pop_back();
    if (its->second.empty())
    {
      Trace("overload") << "** unbind " << d_decls[i] << std::endl;
      d_symTable.erase(its);
    }
  }
  d_decls.resize(lastSize);
}

void State::pushAssumptionScope()
{
  // push scope
  pushScope();
  // remember assumption size
  d_assumptionsSizeCtx.push_back(d_assumptions.size());
}

void State::popAssumptionScope()
{
  // process assumptions
  size_t lastSize = d_assumptionsSizeCtx.back();
  d_assumptionsSizeCtx.pop_back();
  d_assumptions.resize(lastSize);
  // pop the parsing scope
  popScope();
}
bool State::includeFile(const std::string& s, bool isSignature)
{
  return includeFile(s, isSignature, false, d_null);
}
bool State::includeFile(const std::string& s, bool isSignature, bool isReference, const Expr& referenceNf)
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
  if (d_plugin != nullptr)
  {
    if (d_plugin->includeFile(
            inputPath, isSignature, isReference, referenceNf))
    {
      d_inputFile = currentPath;
      Trace("state") << "Include " << inputPath
                     << " handled by plugin" << std::endl;
      return true;
    }
  }
  Trace("state") << "Include " << inputPath << std::endl;
  Assert (getAssumptionLevel()==0);
  if (d_fileReader == nullptr)
  {
    EO_FATAL() << "Error: no file reader set when including " << inputPath;
  }
  d_fileReader->readFile(*this, inputPath, isSignature, isReference);
  d_inputFile = currentPath;
  Trace("state") << "...finished" << std::endl;
  if (d_plugin != nullptr)
  {
    d_plugin->finalizeIncludeFile(
        inputPath, isSignature, isReference, referenceNf);
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

void State::clearReferenceAsserts()
{
  d_referenceAsserts.clear();
  d_referenceAssertList.clear();
}

bool State::setLiteralTypeRule(Kind k, const Expr& t, std::ostream* out)
{
  if (!d_tc.setLiteralTypeRule(k, t, out))
  {
    return false;
  }
  if (d_plugin!=nullptr)
  {
    d_plugin->setLiteralTypeRule(k, t);
  }
  return true;
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

Expr State::mkFunctionType(const std::vector<Expr>& args, const Expr& ret)
{
  if (args.empty())
  {
    return ret;
  }
  Expr curr = ret;
  // no way to construct quote types, e.g. on return types
  Assert (ret.getKind()!=Kind::QUOTE_TYPE);
  for (size_t i=0, nargs = args.size(); i<nargs; i++)
  {
    Expr a = args[(nargs-1)-i];
    // append the function
    curr = Expr(
        mkExprInternal(Kind::FUNCTION_TYPE, {a.getValue(), curr.getValue()}));
  }
  return curr;
}

Expr State::mkProgramType(const std::vector<Expr>& args, const Expr& ret)
{
  Assert(!args.empty());
  std::vector<ExprValue*> atypes;
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    atypes.push_back(args[i].getValue());
  }
  atypes.push_back(ret.getValue());
  return Expr(mkExprInternal(Kind::PROGRAM_TYPE, atypes));
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
  return Expr(mkExpr(Kind::EVAL_REQUIRES, {a1, a2, ret}));
}

Expr State::mkBoolType()
{
  return d_boolType;
}

Expr State::mkListType() { return d_listType; }

Expr State::mkListCons() { return d_listCons; }
Expr State::mkListNil() { return d_listNil; }

Expr State::mkProofType() { return d_proofType; }

Expr State::mkProof(const Expr& proven)
{
  return Expr(mkExprInternal(Kind::PROOF, {proven.getValue()}));
}

Expr State::mkQuoteType(const Expr& t)
{
  Assert(t.getKind() == Kind::PARAM);
  return Expr(mkExprInternal(Kind::QUOTE_TYPE, {t.getValue()}));
}

Expr State::mkSymbol(Kind k, const std::string& name, const Expr& type)
{
  return Expr(mkSymbolInternal(k, name, type));
}

Expr State::mkSelf() const { return d_self; }

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
    // Note that the desugaring of applications based on the attributes of
    // the head (e.g. :right-assoc-nil) is done by the parser, see
    // TermBuilder in parser/term_builder.h.
    ExprValue* hd = vchildren[0];
    Kind hk = hd->getKind();
    if (hk==Kind::LAMBDA)
    {
      // beta-reduce eagerly, if the correct arity
      Expr ret = mkBetaReduceInternal(vchildren);
      if (!ret.isNull())
      {
        return ret;
      }
      Warning() << "Wrong number of arguments when applying " << Expr(hd) << std::endl;
    }
    else if (hk == Kind::PROGRAM_CONST)
    {
      // have to check whether we have marked the constructor kind, which is
      // not the case i.e. if we are constructing applications corresponding to
      // the cases in the program definition itself.
      if (getAttributeKind(hd) != Attr::NONE)
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
        else
        {
          Warning() << "Wrong number of arguments when applying program " << Expr(hd)
                    << ", " << t.getNumChildren() << " arguments expected, got "
                    << children.size() << std::endl;
        }
      }
    }
    // Most functions are unary and require currying if applied to more than one argument.
    // The exceptions to this are operators whose types are not flattened (programs and proof rules).
    if (children.size()>2)
    {
      if (hk != Kind::PROGRAM_CONST && hk != Kind::PROOF_RULE)
      {
        // return the curried version
        return Expr(mkApplyInternal(vchildren));
      }
    }
  }
  else if (isLiteralOp(k))
  {
    // this transforms e.g. (eo::add t1 t2 t3) into (eo::add (eo::add t1 t2)
    // t3).
    if (isNaryLiteralOp(k) && vchildren.size() > 2)
    {
      std::vector<Expr> cc{children[0], children[1]};
      Expr curr = mkExpr(k, cc);
      for (size_t i = 2, nargs = vchildren.size(); i < nargs; i++)
      {
        cc[0] = curr;
        cc[1] = children[i];
        curr = mkExpr(k, cc);
      }
      return curr;
    }
    // only if correct arity, else we will catch the type error
    bool isArityOk = TypeChecker::checkArity(k, vchildren.size());
    if (isArityOk)
    {
      // return the evaluation
      return d_tc.evaluateLiteralOp(k, vchildren);
    }
    else
    {
      Warning() << "Wrong number of arguments when applying literal op " << k
                << ", " << children.size() << " arguments" << std::endl;
    }
  }
  return Expr(mkExprInternal(k, vchildren));
}

Expr State::mkRawExpr(Kind k, const std::vector<Expr>& children)
{
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  return Expr(mkExprInternal(k, vchildren));
}

Expr State::mkTrue() const { return d_true; }

Expr State::mkFalse() const { return d_false; }

Expr State::mkBool(bool val) const { return val ? d_true : d_false; }

Expr State::mkAny() const { return d_any; }

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
      EO_FATAL() << "Unknown kind for mkLiteral " << k;
      break;
  }
  return Expr(mkLiteralInternal(lit));
}

Expr State::mkParameterized(const ExprValue* hd, const std::vector<Expr>& params)
{
  return mkExpr(Kind::PARAMETERIZED, {mkExpr(Kind::TUPLE, params), Expr(hd)});
}

Expr State::mkList(const std::vector<Expr>& args)
{
  // construct (eo::List::cons a1 (eo::List::cons a2 ... eo::List::nil))
  // directly, i.e. without relying on the desugaring of eo::List::cons.
  ExprValue* cons = d_listCons.getValue();
  ExprValue* curr = d_listNil.getValue();
  for (size_t i = args.size(); i > 0; i--)
  {
    ExprValue* ca = mkExprInternal(Kind::APPLY, {cons, args[i - 1].getValue()});
    curr = mkExprInternal(Kind::APPLY, {ca, curr});
  }
  return Expr(curr);
}

Expr State::mkDisambiguatedType(const Expr& disambPat,
                                const Expr& ret,
                                const std::string& name)
{
  // For example, for the ambiguous datatype constructor
  //   (declare-datatypes ((List 1)) (
  //     (par (X) ((nil) (cons (head X) (tail (List X)))))))
  // nil is an ambiguous constructor, which will be written as
  // (as nil (List Int)), which is interpretted as opaque application.
  // To define the type of nil, we first define the program to compute its
  // return type:
  //   (program $eo_disamb_type_nil ((T Type))
  //     :signature (Type) Type
  //     ((($eo_disamb_type_nil (List T)) (List T))))
  // Then, its return type becomes an invocation of this program, where
  // its type is the same as if it were declared via:
  //   (declare-parameterized-const nil ((T Type :opaque))
  //     ($eo_disamb_type_nil T)).
  Expr pt = mkProgramType({d_type}, d_type);
  std::stringstream ss;
  ss << "$eo_disamb_type_" << name;
  Expr tprog = mkSymbol(Kind::PROGRAM_CONST, ss.str(), pt);
  Expr tpat = mkExpr(Kind::APPLY, {tprog, disambPat});
  Expr progCase = mkPair(tpat, ret);
  Expr prog = mkExpr(Kind::PROGRAM, {progCase});
  defineProgram(tprog, prog);
  ss << "_var";
  Expr tv = mkSymbol(Kind::PARAM, ss.str(), d_type);
  Expr qtv = mkQuoteType(tv);
  Expr fapp = mkExpr(Kind::APPLY, {tprog, tv});
  return mkFunctionType({qtv}, fapp);
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
      EO_FATAL() << "Unknown kind for mkLiteralInternal " << l.getKind();
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
  if (d_plugin!=nullptr)
  {
    d_plugin->bind(name, e);
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
  // otherwise use the main symbol table, where we remember previous bindings
  std::vector<Expr>& bs = d_symTable[name];
  if (!bs.empty())
  {
    Trace("overload") << "** overload: " << name << std::endl;
  }
  bs.emplace_back(e);
  // only have to remember if not at global scope
  if (!d_declsSizeCtx.empty())
  {
    d_decls.emplace_back(name);
  }
  return true;
}

Attr State::getAttributeKind(const ExprValue* v) const
{
  const AppInfo* ai = getAppInfo(v);
  if (ai!=nullptr)
  {
    return ai->d_attrCons;
  }
  return Attr::NONE;
}

Expr State::getAttributeTerm(const ExprValue* v) const
{
  const AppInfo* ai = getAppInfo(v);
  if (ai != nullptr)
  {
    return ai->d_attrConsTerm;
  }
  return d_null;
}

Expr State::getVar(const std::string& name) const
{
  std::map<std::string, std::vector<Expr>>::const_iterator it =
      d_symTable.find(name);
  if (it != d_symTable.end())
  {
    return it->second.back();
  }
  return d_null;
}

const std::vector<Expr>* State::getBindings(const std::string& name) const
{
  std::map<std::string, std::vector<Expr>>::const_iterator it =
      d_symTable.find(name);
  if (it != d_symTable.end())
  {
    return &it->second;
  }
  return nullptr;
}

Expr State::getBoundVar(const std::string& name, const Expr& type)
{
  // Variables are not atomic terms. instead, they are terms with two
  // children (string, type). Note this means that (eo::var s T) is an
  // ordinary non-evaluable term, even if s or T is non-ground. This allows
  // variables to be matched on.
  Expr ename = mkLiteral(Kind::STRING, name);
  return mkExpr(Kind::VARIABLE, {ename, type});
}

Expr State::getProofRule(const std::string& name) const
{
  if (!d_opts.d_ruleSymTable)
  {
    return getVar(name);
  }
  std::map<std::string, Expr>::const_iterator it = d_ruleSymTable.find(name);
  if (it != d_ruleSymTable.end())
  {
    return it->second;
  }
  return d_null;
}

void State::notifyAssume(const std::string& name, Expr& proven, bool isPush)
{
  if (d_plugin != nullptr)
  {
    d_plugin->notifyAssume(name, proven, isPush);
  }
  if (isPush)
  {
    pushAssumptionScope();
  }
}

bool State::notifyStep(const std::string& name,
                       Expr& rule,
                       Expr& proven,
                       std::vector<Expr>& premises,
                       std::vector<Expr>& args,
                       bool isPop,
                       Expr& result,
                       std::ostream* err)
{
  bool handledByPlugin = false;
  if (d_plugin != nullptr)
  {
    // if the plugin handles it, then take its result
    handledByPlugin = d_plugin->notifyStep(
        name, rule, proven, premises, args, isPop, result, err);
    if (handledByPlugin)
    {
      // successful if the result is non-null and fully evaluated
      if (result.isNull() || result.isEvaluatable())
      {
        return false;
      }
    }
  }
  if (!handledByPlugin)
  {
    AppInfo* ainfo = getAppInfo(rule.getValue());
    if (ainfo == nullptr)
    {
      if (err)
      {
        (*err) << "Provided :rule is not recognized as a proof rule"
               << std::endl;
      }
      return false;
    }
    std::vector<Expr> children;
    Assert (ainfo->d_attrCons == Attr::PROOF_RULE);
    Expr tupleVal = ainfo->d_attrConsTerm;
    Assert(tupleVal.getNumChildren() == 4);
    // first, we add the program or definition (the latter case is used for
    // proof rules with no arguments or premises).
    children.emplace_back(tupleVal[3]);
    // arguments first
    children.insert(children.end(), args.begin(), args.end());
    bool isAssume = tupleVal[1]==d_true;
    bool isConcExplicit = tupleVal[2]==d_true;
    if (isConcExplicit)
    {
      if (proven.isNull())
      {
        if (err)
        {
          (*err) << "Rules with :conclusion-explicit require a provided "
                    "conclusion."
                 << std::endl;
        }
        // requires a conclusion to be provided
        return false;
      }
      children.push_back(proven);
    }
    if (isPop == isAssume)
    {
      if (isPop)
      {
        std::vector<Expr> as = getCurrentAssumptions();
        // The size of assumptions should be one, but may contain more
        // assumptions if e.g. we encountered assume in a nested assumption
        // scope. Nevertheless, as[0] is always the first assumption in
        // the assume-push.
        // push the assumption
        children.push_back(as[0]);
      }
    }
    else
    {
      // using step for a rule requiring an assumption, or step-pop for a rule
      // not requiring an assumption.
      if (err)
      {
        if (isPop)
        {
          (*err) << "step-pop can only be used on rules with :assumption"
                 << std::endl;
        }
        else
        {
          (*err) << "step cannot be used on rules with :assumption"
                 << std::endl;
        }
      }
      return false;
    }
    // Note that if the rule was marked :premise-list, the parser has already
    // combined the premises, see CmdParser.
    children.insert(children.end(), premises.begin(), premises.end());
    if (children.size() > 1)
    {
      // evaluate the program app
      result = d_tc.evaluateProgramApp(children);
      // if error stream is provided, print details on the failure
      if (result.isEvaluatable())
      {
        if (err)
        {
          if (result.getKind() == Kind::APPLY && result[0] == children[0])
          {
            // if the failure was that the program failed to apply, then
            // provide details on expected arguments.
            Expr prog = getProgram(children[0].getValue());
            Assert(prog.getNumChildren() == 1 && prog[0].getNumChildren() == 2);
            std::vector<Expr> eargs;
            for (size_t i = 1, nchild = prog[0][0].getNumChildren(); i < nchild;
                 i++)
            {
              eargs.push_back(prog[0][0][i]);
            }
            (*err) << "Expected args: " << eargs << std::endl;
            std::vector<Expr> pargs(children.begin() + 1, children.end());
            (*err) << "Provided args: " << pargs << std::endl;
          }
          else
          {
            (*err) << "Evaluation failed: " << result << std::endl;
          }
        }
        return false;
      }
    }
    else
    {
      // otherwise a nullary rule
      result = children[0];
    }
    Assert(!result.isNull() && !result.isEvaluatable());
  }
  // A step-pop conclusion is bound after one assumption scope is removed,
  // so it is at level zero when the current level is one.
  d_lastStepProvesFalseAtLevelZero =
      getAssumptionLevel() == (isPop ? 1 : 0) && result == d_false;
  return true;
}

bool State::lastStepProvesFalseAtLevelZero() const
{
  return d_lastStepProvesFalseAtLevelZero;
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

size_t State::getAssumptionLevel() const
{
  return d_assumptionsSizeCtx.size();
}

std::string State::getOpenAssumptionName() const
{
  Assert(!d_declsSizeCtx.empty() && d_declsSizeCtx.back() < d_decls.size());
  return d_decls[d_declsSizeCtx.back()];
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

void State::markProofRuleSorry(const ExprValue * e)
{
  d_pfrSorry.insert(e);
}

bool State::isProofRuleSorry(const ExprValue* e) const
{
  return d_pfrSorry.find(e)!=d_pfrSorry.end();
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

const AppInfo* State::getAppInfo(const ExprValue* e) const
{
  std::map<const ExprValue *, AppInfo>::const_iterator it = d_appData.find(e);
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

void State::setPlugin(Plugin* p)
{
  Assert (p!=nullptr);
  d_plugin = p;
  d_tc.d_plugin = p;
  // call the initialize method of the plugin
  d_plugin->initialize();
}

Plugin* State::getPlugin()
{
  return d_plugin;
}

void State::setFileReader(FileReader* r) { d_fileReader = r; }

void State::bindBuiltin(const std::string& name, Kind k, Attr ac)
{
  // type is irrelevant, assign abstract
  bindBuiltin(name, k, ac, d_any);
}

void State::bindBuiltin(const std::string& name, Kind k, Attr ac, const Expr& t)
{
  Expr c = mkSymbol(Kind::BUILTIN_CONST, name, t);
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
  bindBuiltin("eo::"+name, k, ac);
}

void State::defineProgram(const Expr& v, const Expr& prog)
{
  if (!prog.isNull())
  {
    markConstructorKind(v, Attr::PROGRAM, prog);
  }
  // call even if null
  if (d_plugin!=nullptr)
  {
    d_plugin->defineProgram(v, prog);
  }
}

void State::define(const std::string& name, const Expr& e)
{
  if (d_plugin != nullptr)
  {
    d_plugin->define(name, e);
  }
}

void State::echo(const std::string& msg)
{
  if (d_plugin != nullptr)
  {
    if (!d_plugin->echo(msg))
    {
      // the plugin processed the echo
      return;
    }
  }
  std::cout << msg << std::endl;
}

bool State::markConstructorKind(const Expr& v, Attr a, const Expr& cons)
{
  Expr acons = cons;
  Assert (isSymbol(v.getKind()));
  AppInfo& ai = d_appData[v.getValue()];
  if (ai.d_attrCons != Attr::NONE)
  {
    // note this fails even if we mark the same constructor, e.g. :list twice
    Warning() << "Cannot set the constructor kind for a term more than once ("
              << ai.d_attrCons << " and " << a << ")" << std::endl;
    return false;
  }
  ai.d_attrCons = a;
  ai.d_attrConsTerm = acons;
  if (d_plugin!=nullptr)
  {
    d_plugin->markConstructorKind(v, a, acons);
  }
  return true;
}

Expr State::mkBetaReduceInternal(const std::vector<ExprValue*>& children)
{
  Assert(!children.empty() && children[0]->getKind() == Kind::LAMBDA);
  ExprValue* hd = children[0];
  const std::vector<ExprValue*>& vars = (*hd)[0]->getChildren();
  size_t nvars = vars.size();
  if (nvars != children.size() - 1)
  {
    return d_null;
  }
  Ctx ctx;
  for (size_t i = 0; i < nvars; i++)
  {
    ctx[vars[i]] = children[i + 1];
  }
  Expr ret = d_tc.evaluate((*hd)[1], ctx);
  Trace("state") << "BETA_REDUCE " << Expr((*hd)[1]) << " " << ctx << " = "
                 << ret << std::endl;
  return ret;
}

}  // namespace ethos
