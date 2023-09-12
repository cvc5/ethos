#include "compiler.h"

#include <algorithm>
#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "state.h"

namespace alfc {

CompilerScope::CompilerScope(std::ostream& decl,
                             std::ostream& out,
                             const std::string& prefix,
                             CompilerScope* global,
                             bool progEval) :
d_decl(decl), d_out(out), d_prefix(prefix), d_progEval(progEval), d_idCount(1), d_subscopeCount(1), d_global(global)
{}

CompilerScope::~CompilerScope(){}

size_t CompilerScope::ensureDeclared(const Expr& ev)
{
  const ExprValue * evv = ev.getValue();
  std::map<const ExprValue*, size_t>::iterator it = d_idMap.find(evv);
  if (it!=d_idMap.end())
  {
    return it->second;
  }
  size_t ret = d_idCount;
  d_idCount++;
  d_idMap[evv] = ret;
  d_decl << "  Expr " << d_prefix << ret << ";" << std::endl;
  return ret;
}

void CompilerScope::ensureDeclared(const std::vector<Expr>& ev)
{
  for (const Expr& e : ev)
  {
    ensureDeclared(e);
  }
}

bool CompilerScope::isGlobal() const
{
  return d_global==nullptr;
}

std::string CompilerScope::getNameFor(const Expr& e) const
{
  // the global scope handled ground terms
  if (d_global!=nullptr && e.isGround())
  {
    return d_global->getNameFor(e);
  }
  std::map<const ExprValue*, size_t>::const_iterator it = d_idMap.find(e.getValue());
  Assert(it != d_idMap.end());
  std::stringstream ss;
  ss << d_prefix << it->second;
  return ss.str();
}
size_t CompilerScope::allocateSubscope()
{
  size_t ret = d_subscopeCount;
  d_subscopeCount++;
  return ret;
}

PathTrie::PathTrie(std::ostream& decl, const std::string& prefix) : d_decl(decl), d_prefix(prefix){}

std::string PathTrie::getNameForPath(const std::vector<size_t>& path)
{
  return d_trie.getNameForPath(d_decl, d_prefix, path);
}

void PathTrie::markDeclared(const std::vector<size_t>& path)
{
  PathTrieNode* pt = &d_trie;
  size_t i = 0;
  while (i<path.size())
  {
    pt = &pt->d_children[path[i]];
    i++;
  }
  pt->d_decl = true;
}

std::string PathTrie::PathTrieNode::getNameForPath(std::ostream& osdecl, const std::string& prefix, const std::vector<size_t>& path)
{
  PathTrieNode* pt = this;
  size_t i = 0;
  std::string curr = prefix;
  while (i<path.size())
  {
    pt = &pt->d_children[path[i]];
    std::stringstream cname;
    cname << curr << path[i];
    if (!pt->d_decl)
    {
      pt->d_decl = true;
      osdecl << "  ExprValue* " << cname.str() << " = (*" << curr << ")[" << path[i] << "];" << std::endl;
    }
    curr = cname.str();
    i++;
  }
  while (i<path.size());
  return curr;
}


Compiler::Compiler(State& s) :
  d_state(s), d_tchecker(s.getTypeChecker()), d_nscopes(0), d_global(d_decl, d_init, "_e", nullptr)
{
  d_decl << "std::map<const ExprValue*, size_t> _runId;" << std::endl;
  d_decl << "Ctx _ctxTmp;" << std::endl;
  d_decl << "Expr _etmp;" << std::endl;
  d_decl << "bool _btmp;" << std::endl;
  d_decl << "bool _btmp2;" << std::endl;
  d_decl << "const Literal* _ltmp;" << std::endl;
  d_config << "std::string State::showCompiledFiles()" << std::endl;
  d_config << "{" << std::endl;
  d_config << "  std::stringstream ss;" << std::endl;
  d_configEnd << "  return ss.str();" << std::endl;
  d_configEnd << "}" << std::endl;
  d_init << "void State::run_initialize()" << std::endl;
  d_init << "{" << std::endl;
  d_initEnd << "}" << std::endl;
  d_tc << "Expr TypeChecker::run_getTypeInternal(ExprValue* hdType, const std::vector<ExprValue*>& args, std::ostream* out)" << std::endl;
  d_tc << "{" << std::endl;
  d_tc << "  std::map<const ExprValue*, size_t>::iterator itr = _runId.find(hdType);" << std::endl;
  // ASSERT
  d_tc << "  switch(itr->second)" << std::endl;
  d_tc << "  {" << std::endl;
  d_tcEnd << "  default: break;" << std::endl;
  d_tcEnd << "  }" << std::endl;
  // TODO: write error?
  d_tcEnd << "  return nullptr;" << std::endl;
  d_tcEnd << "}" << std::endl;
  d_eval << "Expr TypeChecker::run_evaluate(ExprValue* e, Ctx& ctx)" << std::endl;
  d_eval << "{" << std::endl;
  d_eval << "  Ctx::iterator itc;" << std::endl;
  d_eval << "  std::map<const ExprValue*, size_t>::iterator itr = _runId.find(e);" << std::endl;
  // ASSERT
  d_eval << "  switch(itr->second)" << std::endl;
  d_eval << "  {" << std::endl;
  d_evalEnd << "  default: break;" << std::endl;
  d_evalEnd << "  }" << std::endl;
  d_evalEnd << "  return nullptr;" << std::endl;
  d_evalEnd << "}" << std::endl;
  d_evalp << "ExprValue* TypeChecker::run_evaluateProgram(const std::vector<ExprValue*>& args, Ctx& ctx)" << std::endl;
  d_evalp << "{" << std::endl;
  d_evalp << "  std::map<const ExprValue*, size_t>::iterator itr = _runId.find(args[0]);" << std::endl;
  // ASSERT
  d_evalp << "  switch(itr->second)" << std::endl;
  d_evalp << "  {" << std::endl;
  d_evalpEnd << "  default: break;" << std::endl;
  d_evalpEnd << "  }" << std::endl;
  // otherwise just return itself (unevaluated)
  d_evalpEnd << "  return nullptr;" << std::endl;
  d_evalpEnd << "}" << std::endl;
}

Compiler::~Compiler(){}

void Compiler::reset()
{
  // TODO?
}
void Compiler::pushScope()
{
  d_nscopes++;
}

void Compiler::popScope()
{
  Assert(d_nscopes > 0);
  d_nscopes--;
}

void Compiler::setLiteralTypeRule(Kind k, const Expr& t)
{
  if (d_nscopes>0)
  {
    return;
  }
  size_t id = writeGlobalExpr(t);
  d_init << "  d_tc.setLiteralTypeRule(Kind::" << k << ", _e" << id << ");" << std::endl;
}

void Compiler::includeFile(const std::string& s)
{
  Assert (d_nscopes==0);
  d_init << "  markIncluded(\"" << s << "\");" << std::endl;
  d_config << "  ss << std::setw(15) << \" \" << \"" << s << "\" << std::endl;" << std::endl;
}

void Compiler::bind(const std::string& name, const Expr& e)
{
  if (d_nscopes>0)
  {
    return;
  }
  // write the code for constructing the expression
  size_t id = writeGlobalExpr(e);
  // bind the symbol
  d_init << "  bind(\"" << name << "\", _e" << id << ");" << std::endl;
  // write its type checker (if necessary)
  ExprValue * t = d_tchecker.lookupType(e.getValue());
  if (t != nullptr)
  {
    writeTypeChecking(d_tc, t);
  }
}

void Compiler::markConstructorKind(const Expr& v, Attr a, const Expr& cons)
{
  if (d_nscopes>0)
  {
    return;
  }
  size_t id = writeGlobalExpr(v);
  size_t idc = 0;
  if (cons!=nullptr)
  {
    idc = writeGlobalExpr(cons);
  }
  d_init << "  markConstructorKind(_e" << id << ", Attr::" << a << ", ";
  if (cons==nullptr)
  {
    d_init << "nullptr";
  }
  else
  {
    d_init << "_e" << idc;
  }
  d_init << ");" << std::endl;
}

void Compiler::defineProgram(const Expr& v, const Expr& prog)
{
  // we define regardless of scope level
  std::ostream& os = d_evalp;
  size_t id = markCompiled(d_init, v);
  std::stringstream osEnd;
  os << "  case " << id << ":" << std::endl;
  os << "  {" << std::endl;
  osEnd << "  }" << std::endl;
  osEnd << "  break;" << std::endl;
    
  // write evaluation for subterms of each case
  size_t ncases = prog.getNumChildren();
  os << "     size_t _i=0;" << std::endl;
  os << "     while (_i<" << ncases << ")" << std::endl;
  os << "     {" << std::endl;
  os << "       _i++;" << std::endl;
  os << "       switch(_i)" << std::endl;
  os << "       {" << std::endl;
  for (size_t i=0; i<ncases; i++)
  {
    const Expr& c = prog[i];
    Trace("compiler") << "writeEvaluate for " << c << std::endl;
    Expr hd = c[0];
    Expr body = c[1];
    os << "       // matching for arguments of " << hd << std::endl;
    os << "       case " << (i+1) << ":" << std::endl;
    os << "       {" << std::endl;

    // compile the evaluation of the body
    writeEvaluate(d_eval, body);
    // write the matching code for the pattern
    std::stringstream decl;
    std::vector<std::string> reqs;
    std::map<const ExprValue*, std::string> varAssign;
    PathTrie pt(decl, "a");
    for (size_t j=1, nchild=hd.getNumChildren(); j<nchild; j++)
    {
      std::vector<size_t> initPath{j};
      std::stringstream ssa;
      decl << "  ExprValue* a" << j << " = args[" << j << "];" << std::endl;
      pt.markDeclared(initPath);
      // write matching code
      writeMatching(hd[j], initPath, pt, reqs, varAssign, "break");
    }
    os << decl.str();
    os << "  // check requirements" << std::endl;
    writeRequirements(os, reqs, "break");
    size_t id = writeGlobalExpr(body);
    if (body.isGround())
    {
      os << "  // return " << body << std::endl;
      os << "  return _e" << id << ".getValue();" << std::endl;
    }
    os << "  // construct the context" << std::endl;
    std::vector<Expr> fvs = Expr::getVariables(body);
    for (std::pair<const ExprValue * const, std::string>& va : varAssign)
    {
      // don't bother assigning variables that don't occur in the body
      if (std::find(fvs.begin(), fvs.end(), va.first)==fvs.end())
      {
        continue;
      }
      size_t id = writeGlobalExpr(va.first);
      os << "  ctx[_e" << id << ".getValue()] = " << va.second << ";" << std::endl;
    }
    os << "  // return " << body << std::endl;
    os << "  return _e" << id << ".getValue();" << std::endl;
    os << "       }" << std::endl;
    os << "       break;" << std::endl;
  }
  os << "       default: break;" << std::endl;
  os << "       }" << std::endl;
  os << "     }" << std::endl;
  os << osEnd.str();
}

void Compiler::defineConstructor(const Expr& c, const std::vector<Expr>& sels)
{
  size_t cid = writeGlobalExpr(c);
  d_init << "  defineConstructor(_e" << cid << ", ";
  writeArgumentList(d_init, sels);
  d_init << ");" << std::endl;
}

void Compiler::defineDatatype(const Expr& d, const std::vector<Expr>& cons)
{
  size_t did = writeGlobalExpr(d);
  d_init << "  defineDatatype(_e" << did << ", ";
  writeArgumentList(d_init, cons);
  d_init << ");" << std::endl;
}

size_t Compiler::markCompiled(std::ostream& os, const Expr& e)
{
  const ExprValue * ev = e.getValue();
  std::map<const ExprValue*, size_t>::iterator it = d_runIdMap.find(ev);
  if (it!=d_runIdMap.end())
  {
    return it->second;
  }
  size_t ret = writeGlobalExpr(e);
  Assert(it != d_global.d_idMap.end());
  os << "  _runId[_e" << ret << ".getValue()] = " << ret << ";" << std::endl;
  d_init << "  _e" << ret << ".setCompiled();" << std::endl;
  d_runIdMap[ev] = ret;
  return ret;
}

size_t Compiler::writeGlobalExpr(const Expr& e)
{
  return writeExprInternal(e, d_global);
}

size_t Compiler::writeExprInternal(const Expr& e, CompilerScope& s)
{
  size_t ret = 0;
  size_t tid = 0;
  std::unordered_set<const ExprValue*> visited;
  std::unordered_set<const ExprValue*>::iterator it;
  std::vector<Expr> visit;
  visit.emplace_back(e);
  std::map<const ExprValue*, size_t>::iterator iti;
  Expr cur;
  const Literal* curLit;
  do
  {
    cur = visit.back();
    bool isg = s.isGlobal() || cur.isGround();
    CompilerScope& cs = isg ? d_global : s;
    const ExprValue * cv = cur.getValue();
    iti = cs.d_idMap.find(cv);
    if (iti!=cs.d_idMap.end())
    {
      ret = iti->second;
      visit.pop_back();
      continue;
    }
    it = visited.find(cv);
    if (it==visited.end())
    {
      visited.insert(cv);
      if (cur.getKind()==Kind::EVAL_IF_THEN_ELSE && cs.d_progEval)
      {
        // only push the condition
        visit.push_back(cur[0]);
      }
      else
      {
        for (size_t i=0, nchildren=cur.getNumChildren(); i<nchildren; i++)
        {
          visit.push_back(cur[i]);
        }
      }
    }
    else
    {
      visit.pop_back();
      // allocate an identifier
      ret = cs.ensureDeclared(cur);
      std::ostream& os = cs.d_out;
      if (isg)
      {
        // If global, write its type as well, separately. The recursion depth here is very limited.
        ExprValue * t = d_tchecker.lookupType(cur.getValue());
        if (t!=nullptr)
        {
          tid = writeGlobalExpr(t);
        }
      }
      Kind ck = cur.getKind();
      if (isLiteral(ck))
      {
        curLit = d_state.getLiteral(cv);
        Assert(curLit != nullptr);
        os << "  " << cs.d_prefix << ret << " = ";
        os << "mkLiteral(Kind::" << cur.getKind() << ", \"" << curLit->toString() << "\").getValue();" << std::endl;
      }
      else if (isSymbol(ck))
      {
        Assert(isg);
        curLit = d_state.getLiteral(cv);
        Assert(curLit != nullptr);
        os << "  " << cs.d_prefix << ret << " = ";
        // special case: d_self
        if (cur==d_state.mkSelf())
        {
          os << "d_self;" << std::endl;
        }
        else
        {
          os << "mkSymbolInternal(Kind::" << cur.getKind() << ", \"" << curLit->toString() << "\", _e" << tid << ");" << std::endl;
        }
      }
      else if (ck==Kind::TYPE)
      {
        os << "  " << cs.d_prefix << ret << " = d_type.getValue();" << std::endl;
      }
      else if (ck==Kind::BOOL_TYPE)
      {
        os << "  " << cs.d_prefix << ret << " = d_boolType.getValue();" << std::endl;
      }
      else if (ck==Kind::NIL)
      {
        os << "  " << cs.d_prefix << ret << " = d_nil.getValue();" << std::endl;
      }
      else if (ck==Kind::EVAL_IF_THEN_ELSE && cs.d_progEval)
      {
        // we have only written the condition
        Expr condc = cur[0];
        std::string cond = s.getNameFor(condc);
        os << "  _ltmp = d_state.getLiteral(" << cond << ".getValue());" << std::endl;
        os << "  _btmp = (_ltmp!=nullptr && _ltmp->d_tag==Literal::BOOL);" << std::endl;
        os << "  _btmp2 = (_btmp && _ltmp->d_bool);" << std::endl;
        std::stringstream osite;
        std::vector<std::string> branches;
        for (size_t i=0; i<2; i++)
        {
          Expr branch = cur[i+1];
          std::vector<Expr> fvs = Expr::getVariables(branch);
          if (fvs.empty())
          {
            // just write the global expression
            writeGlobalExpr(branch);
            branches.push_back(d_global.getNameFor(branch));
            continue;
          }
          // NOTE: this is worst-case exponential size for the C++ code
          // generated, for branches that share subterms. We should factor
          // out common subterms from the branches here.
          // determine if we should compute this branch
          osite << "  if (!_btmp || " << (i==1 ? "!" : "") << "_btmp2)" << std::endl;
          osite << "  {" << std::endl;
          // write the expression in a local scope
          std::stringstream localDecl;
          // make a unique name for the scope
          std::stringstream ss;
          ss<< cs.d_prefix << "_" << cs.allocateSubscope() << "_";
          std::string pprefix(ss.str());
          CompilerScope pscope(localDecl, osite, pprefix, &d_global, true);
          // don't declare the free variables
          pscope.ensureDeclared(fvs);
          // carry the definitions of variables from outer scope
          for (Expr& v : fvs)
          {
            osite << "  " << pscope.getNameFor(v) << " = " << cs.getNameFor(v) << ";" << std::endl;
          }
          writeExprInternal(branch, pscope);
          osite << "  }" << std::endl;
          // provide the declarations
          os << localDecl.str();
          branches.push_back(pscope.getNameFor(branch));
        }
        os << osite.str();
        // put together the result
        os << "  if (!_btmp)" << std::endl;
        os << "  {" << std::endl;
        os << "    " << cs.d_prefix << ret << " = ";
        if (!cs.isGlobal())
        {
          os << "d_state.";
        }
        os << "mkExprInternal(Kind::EVAL_IF_THEN_ELSE, {" << cond << ".getValue(), " << branches[0] << ".getValue(), " << branches[1] << ".getValue()});" << std::endl;
        os << "  }" << std::endl;
        os << "  else" << std::endl;
        os << "  {" << std::endl;
        os << "    " << cs.d_prefix << ret << " = _btmp2 ? " << branches[0] << " : " << branches[1] << ";" << std::endl;
        os << "  }" << std::endl;
      }
      else if (ck==Kind::EVAL_REQUIRES && cs.d_progEval)
      {
        // call mkRequiresType, which simplifies
        std::string a1 = s.getNameFor(cur[0]);
        std::string a2 = s.getNameFor(cur[1]);
        std::string a3= s.getNameFor(cur[2]);
        os << "    " << cs.d_prefix << ret << " = ";
        if (!cs.isGlobal())
        {
          os << "d_state.";
        }
        os << "mkRequires(" << a1 << ", " << a2 << ", " << a3 << ");" << std::endl;
      }
      else
      {
        std::stringstream argList;
        argList << "{";
        for (size_t i=0, nchildren=cur.getNumChildren(); i<nchildren; i++)
        {
          if (i>0)
          {
            argList << ", ";
          }
          // get the compiler scope for the child, which may be the global one
          argList << s.getNameFor(cur[i]) << ".getValue()";
        }
        argList << "}";
        if (cs.d_progEval && ck==Kind::APPLY && cur[0].getKind()==Kind::PROGRAM_CONST)
        {
          // we should just evaluate it if the scope specifies it should be evaluated
          os << "  _ctxTmp.clear();" << std::endl;
          os << "  _etmp = evaluateProgram(" << argList.str() << ", _ctxTmp);" << std::endl;
          os << "  " << cs.d_prefix << ret << " = evaluateInternal(_etmp.getValue(), _ctxTmp);" << std::endl;
        }
        else if (cs.d_progEval && isLiteralOp(ck))
        {
          os << "  " << cs.d_prefix << ret << " = evaluateLiteralOp(Kind::";
          os << cur.getKind() << ", " << argList.str() << ").getValue();" << std::endl;
        }
        else
        {
          os << "  " << cs.d_prefix << ret << " = ";
          if (!cs.isGlobal())
          {
            os << "d_state.";
          }
          os << "mkExprInternal(Kind::" << cur.getKind() << ", " << argList.str() << ");" << std::endl;
          if (isg)
          {
            // cache its type
            ExprValue * t = d_tchecker.lookupType(cur.getValue());
            if (t!=nullptr)
            {
              os << "  d_tc.d_typeCache[" << d_global.d_prefix << ret << ".getValue()] = " << d_global.d_prefix << tid << ";" << std::endl;
            }
          }
        }
      }
    }
  }while(!visit.empty());
  Assert(ret != 0);
  // return the identifier for the initial term
  return ret;
}

void Compiler::writeTypeChecking(std::ostream& os, const Expr& t)
{
  Assert(t != nullptr);
  std::vector<Expr> toVisit;
  toVisit.push_back(t);
  Expr curr;
  do
  {
    curr = toVisit.back();
    toVisit.pop_back();
    if (curr.getKind()!=Kind::FUNCTION_TYPE)
    {
      // only function types need to be written here
      continue;
    }
    const ExprValue * cv = curr.getValue();
    if (d_tcWritten.find(cv)!=d_tcWritten.end())
    {
      // already written
      continue;
    }
    os << "  // type rule for " << curr << std::endl;
    Trace("compiler") << "writeTypeChecking " << curr << std::endl;
    d_tcWritten.insert(cv);
    size_t id = markCompiled(d_init, curr);
    std::stringstream osEnd;
    os << "  case " << id << ":" << std::endl;
    os << "  {" << std::endl;
    osEnd << "  }" << std::endl;
    osEnd << "  break;" << std::endl;

    // if the return type is ground, we don't need to build a context
    // write the free symbols of the return type as (local) variables
    std::stringstream localDecl;
    std::stringstream localImpl;
    std::string pprefix("_p");
    // mark that we want to evaluate
    CompilerScope pscope(localDecl, localImpl, pprefix, &d_global, true);
    // ensure all variables in the type are declared (but not constructed)
    std::vector<Expr> fvs = Expr::getVariables(curr);
    pscope.ensureDeclared(fvs);
    // write the matching
    std::vector<std::string> reqs;
    std::map<const ExprValue*, std::string> varAssign;
    PathTrie pt(pscope.d_decl, "a");
    for (size_t i=0, nargs=curr.getNumChildren()-1; i<nargs; i++)
    {
      Expr pat = curr[i];
      // quote types match the argument of the type
      if (pat.getKind()==Kind::QUOTE_TYPE)
      {
        pat = pat[0];
      }
      pscope.d_decl << "  ExprValue* a" << i << " = args[" << i << "];" << std::endl;
      // write matching code for args[i] against the type argument pat
      std::vector<size_t> initPath{i};
      pt.markDeclared(initPath);
      writeMatching(pat, initPath, pt, reqs, varAssign, "return nullptr");
    }
    if (!reqs.empty())
    {
      localImpl << "  // check requirements" << std::endl;
      writeRequirements(localImpl, reqs, "return nullptr");
    }
    bool usedMatch = false;
    const Expr& retType = curr[curr.getNumChildren()-1];
    std::unordered_set<const ExprValue*> varsAssigned;
    localImpl << "  // assign variables" << std::endl;
    std::vector<Expr> fvsRet = Expr::getVariables(retType);
    std::map<const ExprValue*, size_t>::iterator iti;
    for (std::pair<const ExprValue* const, std::string>& va : varAssign)
    {
      // only matters if it occurs in return type
      if (std::find(fvsRet.begin(), fvsRet.end(), va.first)==fvsRet.end())
      {
        continue;
      }
      usedMatch = true;
      iti = pscope.d_idMap.find(va.first);
      Assert(iti != pscope.d_idMap.end());
      localImpl << "  " << pprefix << iti->second << " = " << va.second << ";" << std::endl;
      varsAssigned.insert(va.first);
    }
    // any variables in return type that were unassigned should be mapped
    // to their original.
    for (const Expr& v : fvsRet)
    {
      if (varAssign.find(v.getValue())!=varAssign.end())
      {
        // was assigned above
        continue;
      }
      size_t id = writeGlobalExpr(v);
      iti = pscope.d_idMap.find(v.getValue());
      Assert(iti != pscope.d_idMap.end());
      localImpl << "  " << pprefix << iti->second << " = _e" << id << ";" << std::endl;
    }
    // TODO: optimization: if free variables only occur in requires conditions,
    // we can set usedMatch to false

    std::string ret;
    localImpl << "  // construct return type" << std::endl;
    // if ground, write the construction of the return type statically in declarations
    // if non-ground, write the construction of the return type locally
    if (usedMatch)
    {
      writeExprInternal(retType, pscope);
      ret = pscope.getNameFor(retType);
      // note this will ensure that the returned term is evaluated
      // note that the returned type is specific to the type rule, thus we
      // don't also compile the return type.
    }
    else
    {
      writeGlobalExpr(retType);
      ret = d_global.getNameFor(retType);
      // we return the return type verbatim, thus it is worthwhile to compile
      // its type checking as well
      toVisit.push_back(retType);
    }
    localImpl << "  return " << ret << ";" << std::endl;
    // now print the declarations + implementation
    os << localDecl.str();
    os << localImpl.str();
    os << osEnd.str();
  }while (!toVisit.empty());
}

void Compiler::writeMatching(const Expr& pat,
                             std::vector<size_t>& initPath,
                             PathTrie& pt,
                             std::vector<std::string>& reqs,
                             std::map<const ExprValue*, std::string>& varAssign,
                             const std::string& failCmd)
{
  std::vector<std::pair<std::vector<size_t>, Expr>> toVisit;
  toVisit.emplace_back(std::pair<std::vector<size_t>, Expr>(initPath, pat));
  std::pair<std::vector<size_t>, Expr> curr;
  std::map<const ExprValue*, std::string>::iterator itv;
  std::ostream& decl = pt.d_decl;
  do
  {
    curr = toVisit.back();
    toVisit.pop_back();
    std::string cterm = pt.getNameForPath(curr.first);
    Expr p = curr.second;
    if (p.getKind()==Kind::PARAM)
    {
      const ExprValue * pv = p.getValue();
      // if we haven't visited yet
      itv = varAssign.find(pv);
      if (itv==varAssign.end())
      {
        // map to the name we already bound
        varAssign[pv] = cterm;
      }
      else
      {
        // requires being equal to what we bound
        std::stringstream sseq;
        sseq << cterm << "==" << itv->second;
        reqs.push_back(sseq.str());
      }
      continue;
    }
    else if (p.isGround())
    {
      // just check equality
      size_t id = writeGlobalExpr(p);
      std::stringstream ssg;
      ssg << cterm  << "==_e" << id << ".getValue()";
      reqs.push_back(ssg.str());
      // nothing else is required
      continue;
    }
    // requires matching kind/number of children
    std::stringstream ssk;
    ssk << cterm << "->getKind()==Kind::" << p.getKind();
    reqs.push_back(ssk.str());
    // must check this eagerly to avoid OOB
    decl << "  if(" << cterm << "->getNumChildren()!=" << p.getNumChildren() << ")" << std::endl;
    decl << "  {" << std::endl;
    decl << "    " << failCmd << ";" << std::endl;
    decl << "  }" << std::endl;
    std::vector<size_t> newPath = curr.first;
    newPath.push_back(0);
    for (size_t i=0, nchild = p.getNumChildren(); i<nchild; i++)
    {
      newPath[newPath.size()-1] = i;
      toVisit.emplace_back(std::pair<std::vector<size_t>, Expr>(newPath, p[i]));
    }
  }while (!toVisit.empty());
}

void Compiler::writeEvaluate(std::ostream& os, const Expr& e)
{
  std::vector<Expr> toVisit;
  toVisit.push_back(e);
  Expr curr;
  do
  {
    curr = toVisit.back();
    toVisit.pop_back();
    if (curr.isGround())
    {
      // ground terms are constructed statically
      writeGlobalExpr(curr);
      continue;
    }
    if (curr.getKind()==Kind::PARAM)
    {
      // don't bother writing evaluation for parameters
      continue;
    }
    if (curr.isProgEvaluatable())
    {
      // if its evaluatable, traverse
      for (size_t i=0, nchildren=curr.getNumChildren(); i<nchildren; i++)
      {
        toVisit.push_back(curr[i]);
      }
      continue;
    }
    const ExprValue * cv = curr.getValue();
    if (d_evalWritten.find(cv)!=d_evalWritten.end())
    {
      // already written
      continue;
    }
    os << "  // evaluation for " << curr << std::endl;
    Trace("compiler") << "writeEvaluate " << curr << std::endl;
    d_evalWritten.insert(cv);
    
    size_t id = markCompiled(d_init, curr);
    std::stringstream osEnd;
    os << "  case " << id << ":" << std::endl;
    os << "  {" << std::endl;
    osEnd << "  }" << std::endl;
    osEnd << "  break;" << std::endl;
    
    // write the free symbols of the return type as (local) variables
    std::stringstream localDecl;
    std::stringstream localImpl;
    std::string pprefix("_p");
    // we won't print program applications due to guard above, but we will
    // want to execute literal operations.
    CompilerScope pscope(localDecl, localImpl, pprefix, &d_global, true);
    std::vector<Expr> fvs = Expr::getVariables(curr);
    std::map<const ExprValue*, size_t>::iterator iti;
    for (const Expr& v : fvs)
    {
      pscope.ensureDeclared(v);
      // set it equal to the context
      size_t gid = writeGlobalExpr(v);
      std::stringstream ssv;
      ssv << "_e" << gid << ".getValue()";
      iti = pscope.d_idMap.find(v.getValue());
      Assert(iti != pscope.d_idMap.end());
      localImpl << "  itc = ctx.find(" << ssv.str() << ");" << std::endl;
      localImpl << "  " << pprefix << iti->second << " = " 
                << "(itc==ctx.end() ? " << ssv.str() << " : itc->second);" << std::endl;
    }
    // now write the expression
    size_t retId = writeExprInternal(curr, pscope);
    localImpl << "  return " << pprefix << retId << ";" << std::endl;
    // now print the declarations + implementation
    os << localDecl.str();
    os << localImpl.str();
    os << osEnd.str();
  }while (!toVisit.empty());
}

std::string Compiler::toString()
{
  std::stringstream ss;
  ss << "#include \"state.h\"" << std::endl;
  ss << "#include \"type_checker.h\"" << std::endl;
  ss << std::endl;
  ss << "namespace alfc {" << std::endl;
  ss << std::endl;
  ss << d_decl.str() << std::endl;
  ss << d_config.str();
  ss << d_configEnd.str() << std::endl;
  ss << d_init.str();
  ss << d_initEnd.str() << std::endl;
  ss << d_tc.str();
  ss << d_tcEnd.str() << std::endl;
  ss << d_eval.str();
  ss << d_evalEnd.str() << std::endl;
  ss << d_evalp.str();
  ss << d_evalpEnd.str() << std::endl;
  ss << "}" << std::endl;
  return ss.str();
}

void Compiler::writeRequirements(std::ostream& os, const std::vector<std::string>& reqs, const std::string& failCmd)
{
  if (reqs.empty())
  {
    return;
  }
  os << "  if (!(";
  bool firstTime = true;
  for (const std::string& r : reqs)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      os << " && ";
    }
    os << r;
  }
  os << "))" << std::endl;
  os << "  {" << std::endl;
  os << "     " << failCmd << ";" << std::endl;
  os << "  }" << std::endl;
}

void Compiler::writeArgumentList(std::ostream& os,
                                 const std::vector<Expr>& args)
{
  os << "{";
  bool firstTime = true;
  for (const Expr& e : args)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      os << ", ";
    }
    size_t id = writeGlobalExpr(e);
    os << "_e" << id;
  }
  os << "}";
}

}  // namespace alfc
