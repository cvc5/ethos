#include "compiler.h"

#include "state.h"
#include <iostream>
#include <algorithm>

namespace alfc {

CompilerScope::CompilerScope(std::ostream& decl,
                             std::ostream& out,
                             const std::string& prefix,
                             CompilerScope* global,
                             bool progEval) :
d_decl(decl), d_out(out), d_prefix(prefix), d_idCount(1), d_progEval(progEval), d_global(global)
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
  // Assert(it!=d_idMap.end());
  std::stringstream ss;
  ss << d_prefix << it->second;
  return ss.str();
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


Compiler::Compiler(State& s) :
  d_state(s), d_tchecker(s.getTypeChecker()), d_nscopes(0), d_global(d_decl, d_init, "_e", nullptr)
{
  d_decl << "std::map<Attr, Expr> _amap;" << std::endl;
  d_decl << "ExprInfo* _einfo;" << std::endl;
  d_decl << "std::map<ExprValue*, size_t> _runId;" << std::endl;
  d_decl << "Ctx _ctx;" << std::endl;
  d_decl << "Expr _etmp;" << std::endl;
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
  d_eval << "Expr TypeChecker::run_evaluate(Expr& e, Ctx& ctx)" << std::endl;
  d_eval << "{" << std::endl;
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
  size_t id = writeGlobalExpr(v);
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
  d_init << "  markAttributes(_e" << id << ", _amap);" << std::endl;
}
void Compiler::defineProgram(const Expr& v, const Expr& prog)
{
  if (d_nscopes>0)
  {
    return;
  }
  size_t vid = writeGlobalExpr(v);
  // ensure the program is defined
  // NOTE: don't need this once programs are always evaluated below
  size_t pid = writeGlobalExpr(prog);
  d_init << "  defineProgram(_e" << vid << ", _e" << pid << ");" << std::endl;
    
  std::stringstream localDecl;
  std::stringstream localImpl;
  std::string pprefix("_p");
  CompilerScope pscope(localDecl, localImpl, pprefix, &d_global);  
  
  // ensure all variables in the type are declared (but not constructed)
  std::vector<Expr> fvs = getFreeSymbols(prog);
  pscope.ensureDeclared(fvs);

  std::ostream& os = d_evalp;
  size_t id = markCompiled(d_init, v);
  std::stringstream osEnd;
  os << "  case " << id << ":" << std::endl;
  os << "  {" << std::endl;
  osEnd << "  }" << std::endl;
  osEnd << "  break;" << std::endl;
  
  
    
  // write evaluation for subterms of each case
  std::vector<Expr>& progChildren = prog->d_children;
  for (Expr& c : progChildren)
  {
    std::cout << "writeEvaluate for " << c << std::endl;
    Expr hd = c->getChildren()[0];
    Expr body = c->getChildren()[1];
    // compile the evaluation of the body
    writeEvaluate(d_eval, body);
  }
  os << localDecl.str();
  os << localImpl.str();
  os << osEnd.str();
}

size_t Compiler::markCompiled(std::ostream& os, const Expr& e)
{
  std::map<ExprValue*, size_t>::iterator it = d_runIdMap.find(e.get());
  if (it!=d_runIdMap.end())
  {
    return it->second;
  }
  size_t ret = writeGlobalExpr(e);
  // Assert (it!=d_global.d_idMap.end());
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
        curInfo = d_state.getInfo(cur);
        // Assert (curInfo!=nullptr);
        os << "  " << cs.d_prefix << ret << " = ";
        os << "mkLiteral(Kind::" << cur->getKind() << ", \"" << curInfo->d_str << "\");" << std::endl;
      }
      else if (isVariable(ck))
      {
        // Assert (isg);
        curInfo = d_state.getInfo(cur);
        // Assert (curInfo!=nullptr);
        os << "  " << cs.d_prefix << ret << " = ";
        os << "mkSymbolInternal(Kind::" << cur->getKind() << ", \"" << curInfo->d_str << "\", _e" << tid << ");" << std::endl;
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
        if (false && cs.d_progEval && ck==Kind::APPLY && children[0]->getKind()==Kind::PROGRAM_CONST)
        {
          // we should just evaluate it if the scope allows it
          //os <<
          os << "  _ctx.clear();" << std::endl;
          os << "  _etmp = evaluateProgram(" << argList.str() << ", _ctx);" << std::endl;
          os << "  " << cs.d_prefix << ret << " = evaluate(_etmp, _ctx);" << std::endl;
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
    std::vector<Expr> fvs = getFreeSymbols(curr);
    pscope.ensureDeclared(fvs);
    // write the matching
    std::vector<std::string> reqs;
    std::map<Expr, std::string> varAssign;
    for (size_t i=0, nargs=children.size()-1; i<nargs; i++)
    {
      Expr pat = children[i];
      // quote types match their arguments
      if (pat->getKind()==Kind::QUOTE_TYPE)
      {
        pat = pat->getChildren()[0];
      }
      std::stringstream ssa;
      ssa << "a" << i;
      pscope.d_decl << "  Expr& " << ssa.str() << " = args[" << i << "];" << std::endl;
      // write matching code
      writeMatching(pat, ssa.str(), pscope, reqs, varAssign, "return nullptr");
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
    bool usedMatch = false;
    Expr& retType = children.back();
    std::unordered_set<Expr> varsAssigned;
    if (!varAssign.empty())
    {
      localImpl << "  // assign variables" << std::endl;
      std::vector<Expr> fvsRet = getFreeSymbols(retType);
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
        // Assert (iti!=pscope.d_idMap.end());
        localImpl << "  " << pprefix << iti->second << " = " << va.second << ";" << std::endl;
        varsAssigned.insert(va.first);
      }
    }
    // handle requires return type inlined
    if (retType->getKind()==Kind::REQUIRES_TYPE)
    {
      do
      {
        // construct each pair
        std::vector<Expr>& rchildren = retType->d_children;
        for (size_t i = 0, nreqs = rchildren.size()-1; i<nreqs; i++)
        {
          Expr& req = rchildren[i];
          localImpl << "  // handle requirement " << req << std::endl;
          std::vector<std::string> vals;
          for (size_t i=0; i<2; i++)
          {
            Expr ei = (*req.get())[i];
            std::string ret;
            if (hasVariable(ei, varsAssigned))
            {
              writeExprInternal(ei, pscope);
              ret = pscope.getNameFor(ei);
            }
            else
            {
              writeGlobalExpr(ei);
              ret = d_global.getNameFor(ei);
            }
            // evaluate if necessary
            if (ei->isEvaluatable())
            {
              localImpl << "  " << ret << " = evaluate(" << ret << ");" << std::endl;
            }
            vals.push_back(ret);
          }
          localImpl << "  if (" << vals[0] << "!=" << vals[1] << ")" << std::endl;
          localImpl << "  {" << std::endl;
          localImpl << "    if (out) { (*out) << \"Failed compiled requirement: \" << " << vals[0] << " << \" == \" << " << vals[1] << "; }" << std::endl;
          localImpl << "    return nullptr;" << std::endl;
          localImpl << "  }" << std::endl;
        }
        // write the requires here
        retType = rchildren[rchildren.size()-1];
      } while (retType->getKind()==Kind::REQUIRES_TYPE);
      // recompute whether the return type has free variables, since they
      // may have only occurred in requirements
      usedMatch = hasVariable(retType, varsAssigned);
    }
    std::string ret;
    localImpl << "  // construct return type" << std::endl;
    // if ground, write the construction of the return type statically in declarations
    // if non-ground, write the construction of the return type locally
    if (usedMatch)
    {
      writeExprInternal(retType, pscope);
      ret = pscope.getNameFor(retType);
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
    // otherwise, we require evaluating it, which we do via the standard
    // call to the type checker.
    // NOTE: if usedMatch=true, we are doing eager construction of unevaluated terms here!
    // alternatively, we could have the above matching compute the context.
    // TODO: The solution is to have writeExprInternal handle evaluation
    if (retType->isEvaluatable())
    {
      std::stringstream ssret;
      ssret << "evaluate(" << ret << ")";
      ret = ssret.str();
    }
    // just return the type constructed above
    localImpl << "  return " << ret << ";" << std::endl;
    // now print the declarations + implementation
    os << localDecl.str();
    os << localImpl.str();
    os << osEnd.str();
  }while (!toVisit.empty());
}

void Compiler::writeMatching(Expr& pat,
                             const std::string& t,
                             CompilerScope& s,
                             std::vector<std::string>& reqs,
                             std::map<Expr, std::string>& varAssign,
                             const std::string& failCmd)
{
  std::vector<std::pair<std::vector<size_t>, Expr>> toVisit;
  toVisit.emplace_back(std::pair<std::vector<size_t>, Expr>({}, pat));
  std::pair<std::vector<size_t>, Expr> curr;
  std::map<ExprValue*, size_t>::const_iterator it;
  std::map<Expr, std::string>::iterator itv;
  std::ostream& decl = s.d_decl;
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
    if (curr->getKind()==Kind::VARIABLE)
    {
      // don't bother writing evaluation for variables
      continue;
    }
    if (curr->isEvaluatable())
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
    std::cout << "writeEvaluate " << curr << std::endl;
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
    CompilerScope pscope(localDecl, localImpl, pprefix, &d_global);
    localImpl << "  Ctx::iterator itc;" << std::endl;
    std::vector<Expr> fvs = getFreeSymbols(curr);
    std::map<ExprValue*, size_t>::iterator iti;
    for (const Expr& v : fvs)
    {
      pscope.ensureDeclared(v.get());
      // set it equal to the context
      size_t gid = writeGlobalExpr(v);
      std::stringstream ssv;
      ssv << "_e" << gid;
      iti = pscope.d_idMap.find(v.get());
      // Assert (iti!=pscope.d_idMap.end());
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


std::vector<Expr> Compiler::getFreeSymbols(const Expr& e) const
{
  std::vector<Expr> ret;
  std::unordered_set<Expr> visited;
  std::vector<Expr> toVisit;
  toVisit.push_back(e);
  Expr cur;
  do
  {
    cur = toVisit.back();
    toVisit.pop_back();
    if (e->isGround())
    {
      continue;
    }
    if (visited.find(cur)!=visited.end())
    {
      continue;
    }
    visited.insert(cur);
    if (cur->getKind()==Kind::VARIABLE)
    {
      ret.push_back(cur);
      continue;
    }
    toVisit.insert(toVisit.end(), cur->d_children.begin(), cur->d_children.end());
  }while (!toVisit.empty());
  return ret;
}

bool Compiler::hasVariable(const Expr& e, const std::unordered_set<Expr>& vars) const
{
  if (vars.empty())
  {
    return false;
  }
  std::unordered_set<Expr> visited;
  std::vector<Expr> toVisit;
  toVisit.push_back(e);
  Expr cur;
  do
  {
    cur = toVisit.back();
    toVisit.pop_back();
    if (e->isGround())
    {
      continue;
    }
    if (visited.find(cur)!=visited.end())
    {
      continue;
    }
    visited.insert(cur);
    if (cur->getKind()==Kind::VARIABLE)
    {
      if (vars.find(cur)!=vars.end())
      {
        return true;
      }
    }
    toVisit.insert(toVisit.end(), cur->d_children.begin(), cur->d_children.end());
  }while (!toVisit.empty());
  return false;
}


}  // namespace alfc
