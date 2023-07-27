#include "compiler.h"

#include "state.h"
#include <iostream>
#include <algorithm>

namespace alfc {

CompilerScope::CompilerScope(std::ostream& decl, std::ostream& out, const std::string& prefix, bool isGlobal) :
  d_decl(decl), d_out(out), d_prefix(prefix), d_idCount(1), d_isGlobal(isGlobal) {}

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

bool CompilerScope::isGlobal() const
{
  return d_isGlobal;
}

std::string CompilerScope::getNameForPath(const std::string& t, const std::vector<size_t>& path)
{
  PathTrie* pt = &d_pathMap[t];
  size_t i = 0;
  std::string curr = t;
  while (i<path.size())
  {
    pt = &pt->d_children[path[i]];
    std::stringstream cname;
    cname << curr << path[i];
    if (!pt->d_decl)
    {
      pt->d_decl = true;
      d_decl << "  Expr& " << cname.str() << " = " << curr << "->getChildren()[" << path[i] << "];" << std::endl;
    }
    curr = cname.str();
    i++;
  }
  while (i<path.size());
  return curr;
}


Compiler::Compiler(State& s) : d_state(s), d_nscopes(0), d_global(d_decl, d_init, "_e", true)
{
  d_decl << "std::map<Attr, Expr> _amap;" << std::endl;
  d_decl << "ExprInfo* _einfo;" << std::endl;
  d_decl << "std::map<ExprValue*, size_t> _runId;" << std::endl;
  d_init << "void State::run_initialize()" << std::endl;
  d_init << "{" << std::endl;
  d_initEnd << "}" << std::endl;
  d_tc << "Expr TypeChecker::run_getTypeInternal(Expr& hdType, std::vector<Expr>& args, std::ostream* out)" << std::endl;
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
  d_eval << "Expr TypeChecker::run_evaluate(Expr& e, std::vector<Expr>& args)" << std::endl;
  d_eval << "{" << std::endl;
  d_eval << "  std::map<ExprValue*, size_t>::iterator itr = _runId.find(e.get());" << std::endl;
  d_eval << "  switch(itr->second)" << std::endl;
  d_eval << "  {" << std::endl;
  d_evalEnd << "  default: break;" << std::endl;
  d_evalEnd << "  }" << std::endl;
  // otherwise just return itself (unevaluated)
  d_evalEnd << "  std::vector<Expr> eargs;" << std::endl;
  d_evalEnd << "  eargs.push_back(e);" << std::endl;
  d_evalEnd << "  eargs.insert(eargs.end(), args.begin(), args.end());" << std::endl;
  d_evalEnd << "  return d_state.mkExprInternal(Kind::APPLY, eargs);" << std::endl;
  d_evalEnd << "}" << std::endl;
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
  // Assert (d_nscopes>0);
  d_nscopes--;
}

void Compiler::includeFile(const std::string& s)
{
  if (d_nscopes>0)
  {
    return;
  }
  d_init << "  includeFileInternal(\"" << s << "\", true);" << std::endl;
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
  // Assert (e->d_type!=nullptr);
  writeTypeChecking(d_tc, e->d_type);
}

void Compiler::markAttributes(const Expr& v, const std::map<Attr, Expr>& attrs)
{
  if (d_nscopes>0)
  {
    return;
  }
  d_init << "  _amap.clear();" << std::endl;
  for (const std::pair<const Attr, Expr>& p : attrs)
  {
    std::stringstream ssa;
    ssa << "Attr::" << p.first;
    if (p.second!=nullptr)
    {
      size_t id = writeGlobalExpr(p.second);
      d_init << "  _amap[" << ssa.str() << "] = _e" << id << ";" << std::endl;
    }
    else
    {
      d_init << "  _amap[" << ssa.str() << "] = nullptr;" << std::endl;
    }
  }
}
void Compiler::defineProgram(const Expr& v, const Expr& prog)
{
  if (d_nscopes>0)
  {
    return;
  }
  // for each case
  /*
  std::vector<Expr>& progChildren = it->second->d_children;
  for (Expr& c : progChildren)
  {

  }
  */
}

size_t Compiler::markCompiled(std::ostream& os, const Expr& e)
{
  std::map<ExprValue*, size_t>::iterator it = d_runIdMap.find(e.get());
  if (it!=d_runIdMap.end())
  {
    return it->second;
  }
  it = d_global.d_idMap.find(e.get());
  // Assert (it!=d_global.d_idMap.end());
  os << "  _runId[_e" << it->second << ".get()] = " << it->second << ";" << std::endl;
  d_init << "  _e" << it->second << "->setFlag(ExprValue::Flag::IS_COMPILED, true);" << std::endl;
  d_runIdMap[e.get()] = it->second;
  return it->second;
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
  ExprInfo* curInfo;
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
      for (Expr& c : children)
      {
        visit.push_back(c.get());
      }
    }
    else
    {
      visit.pop_back();
      // allocate an identifier
      ret = cs.ensureDeclared(cur);
      std::ostream& os = cs.d_out;
      os << "  " << cs.d_prefix << ret << " = ";
      if (!cs.d_isGlobal)
      {
        os << "d_state.";
      }
      os << "mkExprInternal(Kind::" << cur->getKind() << ", {";
      bool firstTime = true;
      for (Expr& c : children)
      {
        if (firstTime)
        {
          firstTime = false;
        }
        else
        {
          os << ", ";
        }
        // get the compiler scope for the child, which may be the global one
        bool isgc = s.isGlobal() || c->isGround();
        CompilerScope& csc = isgc ? d_global : s;
        iti = csc.d_idMap.find(c.get());
        // Assert (iti!=mu.end());
        os << csc.d_prefix << iti->second;
      }
      os << "});" << std::endl;
      // TODO: should hash?
      if (isg)
      {
        // allocate information if necessary
        curInfo = d_state.getInfo(cur);
        if (curInfo!=nullptr)
        {
          os << "  _einfo = &d_exprData[" << d_global.d_prefix << ret << ".get()];" << std::endl;
          os << "  _einfo->d_str = std::string(\"" << curInfo->d_str << "\");" << std::endl;
        }
        // Write its type as well, separately. The recursion depth here is very limited.
        if (cur->d_type!=nullptr)
        {
          tid = writeGlobalExpr(cur->d_type);
          os << "  " << d_global.d_prefix << ret << "->d_type = " << d_global.d_prefix << tid << ";" << std::endl;
        }
      }
    }
  }while(!visit.empty());
  // Assert (ret!=0);
  // return the identifier for the initial term
  return ret;
}

void Compiler::writeTypeChecking(std::ostream& os, const Expr& t)
{
  // Assert (t!=nullptr);
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
    std::cout << "writeTypeChecking " << curr << std::endl;
    d_tcWritten.insert(t.get());
    size_t id = markCompiled(d_init, curr);
    std::stringstream osEnd;
    os << "  case " << id << ":" << std::endl;
    os << "  {" << std::endl;
    osEnd << "  }" << std::endl;
    osEnd << "  break;" << std::endl;

    // if the return type is ground, we don't need to build a context
    std::vector<Expr>& children = curr->d_children;
    Expr& retType = children.back();
    bool isEval = retType->isEvaluatable();
    std::cout << "isEval=" << isEval << std::endl;
    if (isEval)
    {
      os << "  std::vector<Expr> evalArgs;" << std::endl;
    }
    // write the free symbols of the return type as (local) variables
    std::stringstream localDecl;
    std::stringstream localImpl;
    std::string pprefix("_p");
    CompilerScope pscope(localDecl, localImpl, pprefix);
    // write the matching
    std::vector<std::string> reqs;
    std::map<Expr, std::string> varAssign;
    TypeChecker& tc = d_state.getTypeChecker();
    for (size_t i=0, nargs=children.size()-1; i<nargs; i++)
    {
      // ensure all variables are declared (but not constructed)
      std::vector<Expr> fvs = tc.getFreeSymbols(children[i]);
      for (const Expr& v : fvs)
      {
        pscope.ensureDeclared(v.get());
      }
      std::vector<Expr> pats{children[i]};
      std::stringstream ssa;
      ssa << "a" << i;
      pscope.d_decl << "  Expr& " << ssa.str() << " = args[" << i << "];" << std::endl;
      // write matching code
      writeMatching(pats, ssa.str(), pscope, reqs, varAssign);
    }
    if (!reqs.empty())
    {
      localImpl << "  // check requirements" << std::endl;
      localImpl << "  if (!(";
      bool firstTime = true;
      for (const std::string& r : reqs)
      {
        if (firstTime)
        {
          firstTime = false;
        }
        else
        {
          localImpl << " && ";
        }
        localImpl << r;
      }
      localImpl << "))" << std::endl;
      localImpl << "  {" << std::endl;
      localImpl << "     return nullptr;" << std::endl;
      localImpl << "  }" << std::endl;
    }
    localImpl << "  // assign variables" << std::endl;
    std::vector<Expr> fvsRet = tc.getFreeSymbols(retType);
    std::map<ExprValue*, size_t>::iterator iti;
    bool usedMatch = false;
    for (std::pair<const Expr, std::string>& va : varAssign)
    {
      // only matters if it occurs in return type
      if (std::find(fvsRet.begin(), fvsRet.end(), va.first)==fvsRet.end())
      {
        continue;
      }
      usedMatch = true;
      iti = pscope.d_idMap.find(va.first.get());
      // Assert (iti!=pscope.d_idMap.end());
      localImpl << "  " << pprefix << iti->second << " = " << va.second << ";" << std::endl;
    }
    if (!isEval)
    {
      localImpl << "  // construct return type" << std::endl;
      // if ground, write the construction of the return type statically in declarations
      // if non-ground, write the construction of the return type locally
      if (usedMatch)
      {
        size_t retId = writeExprInternal(retType, pscope);
        // just return the id computed above
        localImpl << "  return " << pprefix << retId << ";" << std::endl;
      }
      else
      {
        size_t retId = writeGlobalExpr(retType);
        localImpl << "  return _e" << retId << ";" << std::endl;
        // currying this function will require another type
        toVisit.push_back(retType);
      }
      // now print the declarations + implementation
      os << localDecl.str();
      os << localImpl.str();
    }
    else
    {
      os << "  return run_evaluate();" << std::endl;;
    }
    os << osEnd.str();
  }while (!toVisit.empty());
}

void Compiler::writeMatching(std::vector<Expr>& pats,
                             const std::string& t,
                             CompilerScope& s,
                             std::vector<std::string>& reqs,
                             std::map<Expr, std::string>& varAssign)
{
  if (pats.size()>1)
  {
    // TODO: parallel matching?
    return;
  }
  Expr pat = pats[0];
  std::vector<std::pair<std::vector<size_t>, Expr>> toVisit;
  toVisit.emplace_back(std::pair<std::vector<size_t>, Expr>({}, pat));
  std::pair<std::vector<size_t>, Expr> curr;
  std::map<ExprValue*, size_t>::const_iterator it;
  std::map<Expr, std::string>::iterator itv;
  do
  {
    curr = toVisit.back();
    toVisit.pop_back();
    std::string cterm = s.getNameForPath(t, curr.first);
    const Expr& p = curr.second;
    if (p->getKind()==Kind::VARIABLE)
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
    std::stringstream ssnc;
    ssnc << cterm << "->getNumChildren()==" << p->getNumChildren();
    reqs.push_back(ssnc.str());
    std::vector<size_t> newPath = curr.first;
    newPath.push_back(0);
    for (size_t i=0, nchild = p->getNumChildren(); i<nchild; i++)
    {
      newPath[newPath.size()-1] = i;
      toVisit.emplace_back(std::pair<std::vector<size_t>, Expr>(newPath, (*p.get())[i]));
    }
  }while (!toVisit.empty());
}

size_t Compiler::writeEvaluation(std::ostream& os, const Expr& e)
{
  // Assert (e!=nullptr);
  if (!e->isEvaluatable())
  {
    // unevaluated types just return themselves
    return writeGlobalExpr(e);
  }
  //size_t id = markCompiled(d_init, e);

  return 0;
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
  ss << d_init.str();
  ss << d_initEnd.str() << std::endl;
  ss << d_tc.str();
  ss << d_tcEnd.str() << std::endl;
  ss << d_eval.str();
  ss << d_evalEnd.str() << std::endl;
  ss << "}" << std::endl;
  return ss.str();
}

}  // namespace alfc
