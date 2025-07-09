
void SmtMetaReduce::bind(const std::string& name, const Expr& e)
{
  // NOTE: the code here ensures that (if needed) we can preserve
  // definitions for the final vc, if it is necessary for debugging.
  // Currently however these definitions are already inlined by the
  // Ethos parser. We would need a --preserve-defs option to Ethos
  // to allow this form of debugging.
  if (name.compare(0, 4, "$eo_") == 0 && e.getKind() == Kind::LAMBDA)
  {
    Expr p = e;
    // dummy type
    std::vector<Expr> argTypes;
    Assert(e[0].getKind() == Kind::TUPLE);
    Assert(e[0].getNumChildren() != 0);
    for (size_t i = 0, nargs = e[0].getNumChildren(); i < nargs; i++)
    {
      Expr aa = e[0][i];
      argTypes.push_back(d_tc.getType(aa));
    }
    Expr body = e[1];
    Expr retType = d_tc.getType(body);
    std::cout << "Look at define " << name << std::endl;
    Assert(!retType.isNull()) << "Cannot type check " << body;
    Expr pt = d_state.mkProgramType(argTypes, retType);
    std::cout << "....make program " << name << " for define, prog type is "
              << pt << std::endl;
    // Expr pt = d_state.mkBuiltinType(Kind::LAMBDA);
    Expr tmp = d_state.mkSymbol(Kind::PROGRAM_CONST, name, pt);
    d_progSeen.emplace_back(tmp, p);
  }
}


void SmtMetaReduce::finalizePrograms()
{
  for (const std::pair<Expr, Expr>& p : d_progSeen)
  {
#ifdef PRESERVE_DEFS
    // This is only necessary if we want to preserve definitions
    // in the final VC (see ::bind).
    // We reduce defines to a program e.g.
    // (define foo ((x T)) (bar x))
    //   becomes
    // (program foo ((x T))
    //   :signature (T) (eo::typeof (bar x))
    //   (
    //   ((foo x) (bar x))
    //   )
    // )
    if (p.second.getKind() == Kind::LAMBDA)
    {
      Expr e = p.second;
      Assert(e[0].getKind() == Kind::TUPLE);
      std::vector<Expr> appChildren;
      appChildren.push_back(p.first);
      for (size_t i = 0, nargs = e[0].getNumChildren(); i < nargs; i++)
      {
        appChildren.push_back(e[0][i]);
      }
      Expr progApp = d_state.mkExprSimple(Kind::APPLY, appChildren);
      Expr pcase = d_state.mkPair(progApp, e[1]);
      Expr prog = d_state.mkExprSimple(Kind::PROGRAM, {pcase});
      std::cout << "...do program " << p.first << " / " << prog << " instead"
                << std::endl;
      finalizeProgram(p.first, prog);
      std::cout << "...finished lambda program" << std::endl;
      continue;
    }
#endif
    finalizeProgram(p.first, p.second);
  }
}
