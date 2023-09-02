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

size_t CompilerScope::ensureDeclared(ExprValue* ev)
{
  std::map<ExprValue*, size_t>::iterator it = d_idMap.find(ev);
  if (it!=d_idMap.end())
  {
    return it->second;
  }
  size_t ret = d_idCount;
  d_idCount++;
  d_idMap[ev] = ret;
  d_decl << "  Expr " << d_prefix << ret << ";" << std::endl;
  return ret;
}

void CompilerScope::ensureDeclared(std::vector<Expr>& ev)
{
  for (Expr& e : ev)
  {
    ensureDeclared(e.get());
  }
}

bool CompilerScope::isGlobal() const
{
  return d_global==nullptr;
}

std::string CompilerScope::getNameFor(Expr& e) const
{
  // the global scope handled ground terms
  if (d_global!=nullptr && e->isGround())
  {
    return d_global->getNameFor(e);
  }
  std::map<ExprValue*, size_t>::const_iterator it = d_idMap.find(e.get());
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
      osdecl << "  Expr& " << cname.str() << " = " << curr << "->getChildren()[" << path[i] << "];" << std::endl;
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
  d_decl << "AttrMap _amap;" << std::endl;
  d_decl << "std::map<ExprValue*, size_t> _runId;" << std::endl;
  d_decl << "Ctx _ctxTmp;" << std::endl;
  d_decl << "Expr _etmp;" << std::endl;
  d_decl << "Expr _etmp2;" << std::endl;
  d_decl << "bool _btmp;" << std::endl;
  d_decl << "bool _btmp2;" << std::endl;
  d_decl << "Literal* _ltmp;" << std::endl;
  d_config << "std::string State::showCompiledFiles()" << std::endl;
  d_config << "{" << std::endl;
  d_config << "  std::stringstream ss;" << std::endl;
  d_configEnd << "  return ss.str();" << std::endl;
  d_configEnd << "}" << std::endl;
  d_init << "void State::run_initialize()" << std::endl;
  d_init << "{" << std::endl;
  d_initEnd << "}" << std::endl;
  d_tc << "Expr TypeChecker::run_getTypeInternal(Expr& hdType, const std::vector<Expr>& args, std::ostream* out)" << std::endl;
  d_tc << "{" << std::endl;
  d_tc << "  std::map<ExprValue*, size_t>::iterator itr = _runId.find(hdType.get());" << std::endl;
  // ASSERT
  d_tc << "  switch(itr->second)" << std::endl;
  d_tc << "  {" << std::endl;
  d_tcEnd << "  default: break;" << std::endl;
  d_tcEnd << "  }" << std::endl;
  // TODO: write error?
  d_tcEnd << "  return nullptr;" << std::endl;
  d_tcEnd << "}" << std::endl;
  d_eval << "Expr TypeChecker::run_evaluate(Expr& e, Ctx& ctx)" << std::endl;
  d_eval << "{" << std::endl;
  d_eval << "  Ctx::iterator itc;" << std::endl;
  d_eval << "  std::map<ExprValue*, size_t>::iterator itr = _runId.find(e.get());" << std::endl;
  // ASSERT
  d_eval << "  switch(itr->second)" << std::endl;
  d_eval << "  {" << std::endl;
  d_evalEnd << "  default: break;" << std::endl;
  d_evalEnd << "  }" << std::endl;
  d_evalEnd << "  return nullptr;" << std::endl;
  d_evalEnd << "}" << std::endl;
  d_evalp << "Expr TypeChecker::run_evaluateProgram(const std::vector<Expr>& args, Ctx& ctx)" << std::endl;
  d_evalp << "{" << std::endl;
  d_evalp << "  std::map<ExprValue*, size_t>::iterator itr = _runId.find(args[0].get());" << std::endl;
  // ASSERT
  d_evalp << "  switch(itr->second)" << std::endl;
  d_evalp << "  {" << std::endl;
  d_evalpEnd << "  default: break;" << std::endl;
  d_evalpEnd << "  }" << std::endl;
  // otherwise just return itself (unevaluated)
  d_evalpEnd << "  return d_state.mkExprInternal(Kind::APPLY, args);" << std::endl;
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
  if (d_nscopes>0)
  {
    return;
  }
  d_init << "  markIncluded(\"" << s << "\");" << std::endl;
  d_config << "  ss << std::setw(15) << \" \" << \"" << s << "\" << std::endl;" << std::endl;
}

void Compiler::addAssumption(const Expr& a)
{
  if (d_nscopes>0)
  {
    return;
  }
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
  if (e->d_type != nullptr)
  {
    writeTypeChecking(d_tc, e->d_type);
  }
}

void Compiler::markAttributes(const Expr& v, const AttrMap& attrs)
{
  if (d_nscopes>0)
  {
    return;
  }
  size_t id = writeGlobalExpr(v);
  d_init << "  _amap.clear();" << std::endl;
  for (const std::pair<const Attr, std::vector<Expr>>& p : attrs)
  {
    std::stringstream ssa;
    ssa << "Attr::" << p.first;
    for (const Expr& pv : p.second)
    {
      if (pv!=nullptr)
      {
        size_t id = writeGlobalExpr(pv);
        d_init << "  _amap[" << ssa.str() << "].push_back(_e" << id << ");" << std::endl;
      }
      else
      {
        d_init << "  _amap[" << ssa.str() << "].push_back(nullptr);" << std::endl;
      }
    }
  }
  d_init << "  markAttributes(_e" << id << ", _amap);" << std::endl;
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
  std::vector<Expr>& progChildren = prog->d_children;
  size_t ncases = progChildren.size();
  os << "     size_t _i=0;" << std::endl;
  os << "     while (_i<" << ncases << ")" << std::endl;
  os << "     {" << std::endl;
  os << "       _i++;" << std::endl;
  os << "       switch(_i)" << std::endl;
  os << "       {" << std::endl;
  for (size_t i=0; i<ncases; i++)
  {
    Expr& c = progChildren[i];
    Trace("compiler") << "writeEvaluate for " << c << std::endl;
    Expr hd = c->getChildren()[0];
    Expr body = c->getChildren()[1];
    os << "       // matching for arguments of " << hd << std::endl;
    os << "       case " << (i+1) << ":" << std::endl;
    os << "       {" << std::endl;

    // compile the evaluation of the body
    writeEvaluate(d_eval, body);
    // write the matching code for the pattern
    std::vector<Expr>& children = hd->getChildren();
    std::stringstream decl;
    std::vector<std::string> reqs;
    std::map<Expr, std::string> varAssign;
    PathTrie pt(decl, "a");
    for (size_t j=1, nchild=children.size(); j<nchild; j++)
    {
      std::vector<size_t> initPath{j};
      std::stringstream ssa;
      decl << "  const Expr& a" << j << " = args[" << j << "];" << std::endl;
      pt.markDeclared(initPath);
      // write matching code
      writeMatching(children[j], initPath, pt, reqs, varAssign, "break");
    }
    os << decl.str();
    os << "  // check requirements" << std::endl;
    writeRequirements(os, reqs, "break");
    size_t id = writeGlobalExpr(body);
    if (body->isGround())
    {
      os << "  // return " << body << std::endl;
      os << "  return _e" << id << ";" << std::endl;
    }
    os << "  // construct the context" << std::endl;
    std::vector<Expr> fvs = ExprValue::getVariables(body);
    for (std::pair<const Expr, std::string>& va : varAssign)
    {
      // don't bother assigning variables that don't occur in the body
      if (std::find(fvs.begin(), fvs.end(), va.first)==fvs.end())
      {
        continue;
      }
      size_t id = writeGlobalExpr(va.first);
      os << "  ctx[_e" << id << "] = " << va.second << ";" << std::endl;
    }
    os << "  // return " << body << std::endl;
    os << "  return _e" << id << ";" << std::endl;
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
  std::map<ExprValue*, size_t>::iterator it = d_runIdMap.find(e.get());
  if (it!=d_runIdMap.end())
  {
    return it->second;
  }
  size_t ret = writeGlobalExpr(e);
  Assert(it != d_global.d_idMap.end());
  os << "  _runId[_e" << ret << ".get()] = " << ret << ";" << std::endl;
  d_init << "  _e" << ret << "->setFlag(ExprValue::Flag::IS_COMPILED, true);" << std::endl;
  d_runIdMap[e.get()] = ret;
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
  std::unordered_set<ExprValue*> visited;
  std::unordered_set<ExprValue*>::iterator it;
  std::vector<ExprValue*> visit;
  visit.emplace_back(e.get());
  std::map<ExprValue*, size_t>::iterator iti;
  ExprValue * cur;
  Literal* curLit;
  do
  {
    cur = visit.back();
    bool isg = s.isGlobal() || cur->isGround();
    CompilerScope& cs = isg ? d_global : s;
    iti = cs.d_idMap.find(cur);
    if (iti!=cs.d_idMap.end())
    {
      ret = iti->second;
      visit.pop_back();
      continue;
    }
    it = visited.find(cur);
    std::vector<Expr>& children = cur->d_children;
    if (it==visited.end())
    {
      visited.insert(cur);
      if (cur->getKind()==Kind::EVAL_IF_THEN_ELSE && cs.d_progEval)
      {
        // only push the condition
        visit.push_back(children[0].get());
      }
      else
      {
        for (Expr& c : children)
        {
          visit.push_back(c.get());
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
        if (cur->d_type!=nullptr)
        {
          tid = writeGlobalExpr(cur->d_type);
        }
      }
      Kind ck = cur->getKind();
      if (isLiteral(ck))
      {
        curLit = d_state.getLiteral(cur);
        Assert(curLit != nullptr);
        os << "  " << cs.d_prefix << ret << " = ";
        os << "mkLiteral(Kind::" << cur->getKind() << ", \"" << curLit->toString() << "\");" << std::endl;
      }
      else if (isSymbol(ck))
      {
        Assert(isg);
        curLit = d_state.getLiteral(cur);
        Assert(curLit != nullptr);
        os << "  " << cs.d_prefix << ret << " = ";
        // special case: d_self
        if (cur==d_state.mkSelf().get())
        {
          os << "d_self;" << std::endl;
        }
        else
        {
          os << "mkSymbolInternal(Kind::" << cur->getKind() << ", \"" << curLit->toString() << "\", _e" << tid << ");" << std::endl;
        }
      }
      else if (ck==Kind::TYPE)
      {
        os << "  " << cs.d_prefix << ret << " = d_type;" << std::endl;
      }
      else if (ck==Kind::BOOL_TYPE)
      {
        os << "  " << cs.d_prefix << ret << " = d_boolType;" << std::endl;
      }
      else if (ck==Kind::NIL)
      {
        os << "  " << cs.d_prefix << ret << " = d_nil;" << std::endl;
      }
      else if (ck==Kind::EVAL_IF_THEN_ELSE && cs.d_progEval)
      {
        // we have only written the condition
        std::string cond = s.getNameFor(children[0]);
        os << "  _ltmp = d_state.getLiteral(" << cond << ".get());" << std::endl;
        os << "  _btmp = (_ltmp!=nullptr && _ltmp->d_tag==Literal::BOOL);" << std::endl;
        os << "  _btmp2 = (_btmp && _ltmp->d_bool);" << std::endl;
        std::stringstream osite;
        std::vector<std::string> branches;
        for (size_t i=0; i<2; i++)
        {
          Expr branch = children[i+1];
          std::vector<Expr> fvs = ExprValue::getVariables(branch);
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
        os << "mkExprInternal(Kind::EVAL_IF_THEN_ELSE, {" << cond << ", " << branches[0] << ", " << branches[1] << "});" << std::endl;
        os << "  }" << std::endl;
        os << "  else" << std::endl;
        os << "  {" << std::endl;
        os << "    " << cs.d_prefix << ret << " = _btmp2 ? " << branches[0] << " : " << branches[1] << ";" << std::endl;
        os << "  }" << std::endl;
      }
      else if (ck==Kind::REQUIRES_TYPE && cs.d_progEval)
      {
        // call mkRequiresType, which simplifies
        std::string a1 = s.getNameFor(children[0]);
        std::string a2 = s.getNameFor(children[1]);
        std::string a3= s.getNameFor(children[2]);
        os << "    " << cs.d_prefix << ret << " = ";
        if (!cs.isGlobal())
        {
          os << "d_state.";
        }
        os << "mkRequiresType(" << a1 << ", " << a2 << ", " << a3 << ");" << std::endl;
      }
      else
      {
        std::stringstream argList;
        argList << "{";
        bool firstTime = true;
        for (Expr& c : children)
        {
          if (firstTime)
          {
            firstTime = false;
          }
          else
          {
            argList << ", ";
          }
          // get the compiler scope for the child, which may be the global one
          argList << s.getNameFor(c);
        }
        argList << "}";
        if (cs.d_progEval && ck==Kind::APPLY && children[0]->getKind()==Kind::PROGRAM_CONST)
        {
          // we should just evaluate it if the scope specifies it should be evaluated
          os << "  _ctxTmp.clear();" << std::endl;
          os << "  _etmp = evaluateProgram(" << argList.str() << ", _ctxTmp);" << std::endl;
          os << "  " << cs.d_prefix << ret << " = evaluate(_etmp, _ctxTmp);" << std::endl;
        }
        else if (cs.d_progEval && isLiteralOp(ck))
        {
          os << "  " << cs.d_prefix << ret << " = evaluateLiteralOp(Kind::";
          os << cur->getKind() << ", " << argList.str() << ");" << std::endl;
        }
        else
        {
          os << "  " << cs.d_prefix << ret << " = ";
          if (!cs.isGlobal())
          {
            os << "d_state.";
          }
          os << "mkExprInternal(Kind::" << cur->getKind() << ", " << argList.str() << ");" << std::endl;
          if (isg)
          {
            // cache its type
            if (cur->d_type!=nullptr)
            {
              os << "  " << d_global.d_prefix << ret << "->d_type = " << d_global.d_prefix << tid << ";" << std::endl;
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
    if (curr->getKind()!=Kind::FUNCTION_TYPE)
    {
      // only function types need to be written here
      continue;
    }
    if (d_tcWritten.find(curr.get())!=d_tcWritten.end())
    {
      // already written
      continue;
    }
    os << "  // type rule for " << curr << std::endl;
    Trace("compiler") << "writeTypeChecking " << curr << std::endl;
    d_tcWritten.insert(curr.get());
    size_t id = markCompiled(d_init, curr);
    std::stringstream osEnd;
    os << "  case " << id << ":" << std::endl;
    os << "  {" << std::endl;
    osEnd << "  }" << std::endl;
    osEnd << "  break;" << std::endl;

    // if the return type is ground, we don't need to build a context
    std::vector<Expr>& children = curr->d_children;
    // write the free symbols of the return type as (local) variables
    std::stringstream localDecl;
    std::stringstream localImpl;
    std::string pprefix("_p");
    // mark that we want to evaluate
    CompilerScope pscope(localDecl, localImpl, pprefix, &d_global, true);
    // ensure all variables in the type are declared (but not constructed)
    std::vector<Expr> fvs = ExprValue::getVariables(curr);
    pscope.ensureDeclared(fvs);
    // write the matching
    std::vector<std::string> reqs;
    std::map<Expr, std::string> varAssign;
    PathTrie pt(pscope.d_decl, "a");
    for (size_t i=0, nargs=children.size()-1; i<nargs; i++)
    {
      Expr pat = children[i];
      // quote types match the argument of the type
      if (pat->getKind()==Kind::QUOTE_TYPE)
      {
        pat = pat->getChildren()[0];
      }
      pscope.d_decl << "  const Expr& a" << i << " = args[" << i << "];" << std::endl;
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
    Expr& retType = children.back();
    std::unordered_set<Expr> varsAssigned;
    localImpl << "  // assign variables" << std::endl;
    std::vector<Expr> fvsRet = ExprValue::getVariables(retType);
    std::map<ExprValue*, size_t>::iterator iti;
    for (std::pair<const Expr, std::string>& va : varAssign)
    {
      // only matters if it occurs in return type
      if (std::find(fvsRet.begin(), fvsRet.end(), va.first)==fvsRet.end())
      {
        continue;
      }
      usedMatch = true;
      iti = pscope.d_idMap.find(va.first.get());
      Assert(iti != pscope.d_idMap.end());
      localImpl << "  " << pprefix << iti->second << " = " << va.second << ";" << std::endl;
      varsAssigned.insert(va.first);
    }
    // any variables in return type that were unassigned should be mapped
    // to their original.
    for (const Expr& v : fvsRet)
    {
      if (varAssign.find(v)!=varAssign.end())
      {
        // was assigned above
        continue;
      }
      size_t id = writeGlobalExpr(v);
      iti = pscope.d_idMap.find(v.get());
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

void Compiler::writeMatching(Expr& pat,
                             std::vector<size_t>& initPath,
                             PathTrie& pt,
                             std::vector<std::string>& reqs,
                             std::map<Expr, std::string>& varAssign,
                             const std::string& failCmd)
{
  std::vector<std::pair<std::vector<size_t>, Expr>> toVisit;
  toVisit.emplace_back(std::pair<std::vector<size_t>, Expr>(initPath, pat));
  std::pair<std::vector<size_t>, Expr> curr;
  std::map<ExprValue*, size_t>::const_iterator it;
  std::map<Expr, std::string>::iterator itv;
  std::ostream& decl = pt.d_decl;
  do
  {
    curr = toVisit.back();
    toVisit.pop_back();
    std::string cterm = pt.getNameForPath(curr.first);
    const Expr& p = curr.second;
    if (p->getKind()==Kind::PARAM)
    {
      // if we haven't visited yet
      itv = varAssign.find(p);
      if (itv==varAssign.end())
      {
        // map to the name we already bound
        varAssign[p] = cterm;
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
    else if (p->isGround())
    {
      // just check equality
      size_t id = writeGlobalExpr(p);
      std::stringstream ssg;
      ssg << cterm  << "==_e" << id;
      reqs.push_back(ssg.str());
      // nothing else is required
      continue;
    }
    // requires matching kind/number of children
    std::stringstream ssk;
    ssk << cterm << "->getKind()==Kind::" << p->getKind();
    reqs.push_back(ssk.str());
    // must check this eagerly to avoid OOB
    decl << "  if(" << cterm << "->getNumChildren()!=" << p->getNumChildren() << ")" << std::endl;
    decl << "  {" << std::endl;
    decl << "    " << failCmd << ";" << std::endl;
    decl << "  }" << std::endl;
    std::vector<size_t> newPath = curr.first;
    newPath.push_back(0);
    for (size_t i=0, nchild = p->getNumChildren(); i<nchild; i++)
    {
      newPath[newPath.size()-1] = i;
      toVisit.emplace_back(std::pair<std::vector<size_t>, Expr>(newPath, (*p.get())[i]));
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
    if (curr->isGround())
    {
      // ground terms are constructed statically
      writeGlobalExpr(curr);
      continue;
    }
    if (curr->getKind()==Kind::PARAM)
    {
      // don't bother writing evaluation for parameters
      continue;
    }
    if (curr->isProgEvaluatable())
    {
      // if its evaluatable, traverse
      std::vector<Expr>& children = curr->d_children;
      toVisit.insert(toVisit.end(), children.begin(), children.end());
      continue;
    }
    if (d_evalWritten.find(curr.get())!=d_evalWritten.end())
    {
      // already written
      continue;
    }
    os << "  // evaluation for " << curr << std::endl;
    Trace("compiler") << "writeEvaluate " << curr << std::endl;
    d_evalWritten.insert(curr.get());
    
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
    std::vector<Expr> fvs = ExprValue::getVariables(curr);
    std::map<ExprValue*, size_t>::iterator iti;
    for (const Expr& v : fvs)
    {
      pscope.ensureDeclared(v.get());
      // set it equal to the context
      size_t gid = writeGlobalExpr(v);
      std::stringstream ssv;
      ssv << "_e" << gid;
      iti = pscope.d_idMap.find(v.get());
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
