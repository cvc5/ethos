/******************************************************************************
 * This file is part of the ethos project.
 * See COPYING for licensing information.
 ******************************************************************************/
#include "rust_meta_reduce.h"

#include <fstream>
#include <iomanip>
#include <sstream>

#include "literal.h"

namespace ethos {

namespace {
bool starts(const std::string& s, const std::string& p)
{
  return s.compare(0, p.size(), p) == 0;
}
std::string read(const std::string& path)
{
  std::ifstream in(path);
  if (!in) { EO_FATAL() << "rust-meta: cannot read " << path; }
  std::ostringstream out;
  out << in.rdbuf();
  return out.str();
}
}  // namespace

RustMetaReduce::RustMetaReduce(State& s) : MetaReducePlugin(s)
{
  d_typeToMetaKind["$eo_Term"] = MetaKind::EUNOIA;
  d_typeToMetaKind["$eo_Proof"] = MetaKind::PROOF;
  d_typeToMetaKind["$eo_Rule"] = MetaKind::CHECKER_RULE;
  d_typeToMetaKind["$eo_Cmd"] = MetaKind::CHECKER_CMD;
}

std::string RustMetaReduce::ident(const std::string& name)
{
  std::ostringstream out;
  out << "eo_";
  for (unsigned char c : name)
  {
    if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9')) { out << c; }
    else { out << '_' << std::hex << std::setw(2) << std::setfill('0') << unsigned(c); }
  }
  return out.str();
}

std::string RustMetaReduce::quote(const std::string& text)
{
  std::ostringstream out;
  out << '"';
  for (unsigned char c : text)
  {
    if (c == '"' || c == '\\') { out << '\\' << c; }
    else if (c >= 32 && c <= 126) { out << c; }
    else { out << "\\u{" << std::hex << unsigned(c) << '}'; }
  }
  out << '"';
  return out.str();
}

Kind RustMetaReduce::builtin(const std::string& name)
{
  // Signature-dependent metadata is compiled, including typeof and nil.
  if (!starts(name, "$eo_")) { return Kind::NONE; }
  for (int i = int(Kind::EVAL_IS_OK); i <= int(Kind::EVAL_DT_SELECTORS); ++i)
  {
    Kind k = static_cast<Kind>(i);
    if (k == Kind::EVAL_TYPE_OF || k == Kind::EVAL_NIL
        || k == Kind::EVAL_DT_CONSTRUCTORS || k == Kind::EVAL_DT_SELECTORS) { continue; }
    if (kindToTerm(k) == "eo::" + name.substr(4)) { return k; }
  }
  return Kind::NONE;
}

bool RustMetaReduce::isBuiltinMetaSymbol(const std::string& name) const
{
  return starts(name, "$native_") || d_typeToMetaKind.count(name) != 0;
}

void RustMetaReduce::finalizeDecl(const Expr& e)
{
  const std::string name = getName(e);
  if (starts(name, "$native_") || !beginFinalizeDecl(e)) { return; }
  Expr ty = e.getType();
  size_t arity = d_state.getAttributeKind(e.getValue()) == Attr::OPAQUE
                     ? ty.getNumChildren() - 1 : 0;
  bool object = !starts(name, "$emb_")
                || (name.find('.') == std::string::npos && name != "$eo_pf");
  d_constructorOrder.push_back(name);
  d_constructors.emplace(name, Constructor{arity, object});
}

void RustMetaReduce::defineProgram(const Expr& v, const Expr& prog)
{
  if (!prog.isNull()) { d_programs[getName(v)] = {v, prog, false}; }
}

void RustMetaReduce::define(const std::string& name, const Expr& e)
{
  if (!starts(name, "$eo_") || !getEmbedTypeApp(e).isNull()) { return; }
  Expr symbol, prog;
  if (buildLambdaDefineProgram(name, e, symbol, prog))
  {
    d_programs[name] = {symbol, prog, true};
  }
  else { d_programs[name] = {e, e, true}; }
}

bool RustMetaReduce::echo(const std::string& msg)
{
  if (starts(msg, "lean-parser-op "))
  {
    std::istringstream in(msg.substr(15));
    std::string surface, name, arity, index, attr;
    if (in >> surface >> name >> arity >> index >> attr && starts(attr, "left-assoc"))
    {
      d_leftAssoc.insert(name);
    }
  }
  return false;
}

std::set<std::string> RustMetaReduce::reachable() const
{
  const std::set<std::string> roots{
      "$eo_checker_is_refutation", "$eo_invoke_cmd_list", "$eo_invoke_assume_list",
      "$eo_state_is_refutation", "$eo_typeof", "$eo_nil", "$eo_is_list_nil",
      "$eo_dt_constructors", "$eo_dt_selectors", "$eo_to_smt", "$eo_to_smt_type",
      "$smtx_typeof", "$smtx_type_wf", "$smtx_type_wf_component"};
  std::vector<std::string> todo;
  for (const auto& p : d_programs)
  {
    if (starts(p.first, "$eo_prog_") || roots.count(p.first)) { todo.push_back(p.first); }
  }
  std::set<std::string> seen;
  while (!todo.empty())
  {
    std::string name = todo.back();
    todo.pop_back();
    if (builtin(name) != Kind::NONE || !seen.insert(name).second) { continue; }
    auto p = d_programs.find(name);
    if (p == d_programs.end()) { EO_FATAL() << "rust-meta: undefined reachable program " << name; }
    std::vector<Expr> terms{p->second.body};
    std::set<Expr> visited;
    while (!terms.empty())
    {
      Expr e = terms.back();
      terms.pop_back();
      if (!visited.insert(e).second) { continue; }
      if (e.getKind() == Kind::PROGRAM_CONST) { todo.push_back(getName(e)); }
      for (size_t i = 0; i < e.getNumChildren(); ++i) { terms.push_back(e[i]); }
    }
  }
  return seen;
}

std::string RustMetaReduce::schema() const
{
  std::ostringstream out;
  out << "#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]\npub enum Constructor {\n";
  for (const auto& c : d_constructors) { out << ident(c.first) << ",\n"; }
  out << "}\nimpl Constructor {\npub fn name(self) -> &'static str { match self {\n";
  for (const auto& c : d_constructors) { out << "Self::" << ident(c.first) << " => " << quote(c.first) << ",\n"; }
  out << "}}\npub fn from_name(name: &str) -> Option<Self> { Some(match name {\n";
  for (const auto& c : d_constructors) { out << quote(c.first) << " => Self::" << ident(c.first) << ",\n"; }
  out << "_ => return None, }) }\npub fn arity(self) -> usize { match self {\n";
  for (const auto& c : d_constructors) { out << "Self::" << ident(c.first) << " => " << c.second.arity << ",\n"; }
  out << "}}\npub fn is_object(self) -> bool { match self {\n";
  for (const auto& c : d_constructors) { out << "Self::" << ident(c.first) << " => " << (c.second.isObject ? "true" : "false") << ",\n"; }
  out << "}}\npub fn is_left_assoc(self) -> bool { match self.name() {\n";
  for (const auto& n : d_leftAssoc) { out << quote(n) << " => true,\n"; }
  out << "_ => false, }}\npub fn order_key(self) -> (usize, usize) { match self {\n";
  std::map<std::string, size_t> tags;
  size_t next = 0;
  const std::set<std::string> metaTypes{"$eo_Term", "$eo_Rule", "$eo_Cmd", "$eo_Proof", "$eo_pf"};
  for (const std::string& name : d_constructorOrder)
  {
    if ((starts(name, "$emb_") && name.find('.') == std::string::npos)
        || (starts(name, "$eo_") && !metaTypes.count(name))) { tags[name] = next++; }
  }
  std::map<size_t, size_t> users;
  std::map<std::string, size_t> datatypes;
  for (const std::string& name : d_constructorOrder)
  {
    size_t arity = d_constructors.at(name).arity;
    size_t tag, subtag = 0;
    if (tags.count(name)) { tag = tags.at(name); }
    else if (!starts(name, "$emb_") && !starts(name, "$eo_"))
    {
      std::string wrapper = "$emb_UOp" + (arity == 0 ? "" : std::to_string(arity));
      tag = tags.count(wrapper) ? tags.at(wrapper) : next;
      subtag = users[arity]++;
    }
    else { tag = datatypes[name.substr(0, name.find('.'))]++; }
    out << "Self::" << ident(name) << " => (" << tag << ", " << subtag << "),\n";
  }
  out << "}}\n}\n";
  return out.str();
}

std::string RustMetaReduce::literal(const Expr& e)
{
  const Literal* l = e.getValue()->asLiteral();
  std::ostringstream out;
  switch (e.getKind())
  {
    case Kind::BOOLEAN: return l->d_bool ? "Lit::Bool(true)" : "Lit::Bool(false)";
    case Kind::NUMERAL: return "Lit::Numeral(parse_int(" + quote(l->d_int.toString()) + ")?)";
    case Kind::RATIONAL:
    case Kind::DECIMAL: return "Lit::Rational(parse_rat(" + quote(l->d_rat.toString()) + ")?)";
    case Kind::BINARY:
    case Kind::HEXADECIMAL:
      out << "Lit::Binary(BitVec::new(" << l->d_bv.getSize() << ", &parse_int("
          << quote(l->d_bv.getValue().toString()) << ")?))";
      return out.str();
    case Kind::STRING:
      out << "Lit::String(EoString::from_code_points(vec![";
      for (unsigned c : l->d_str.getValue()) { out << c << ','; }
      out << "]))";
      return out.str();
    default: EO_FATAL() << "rust-meta: unsupported literal " << e;
  }
  return "";
}

/** Emits temporaries in evaluation order; no nested mutable borrows. */
class RustMetaReduce::Emitter
{
 public:
  Emitter(RustMetaReduce& meta, std::ostream& out) : m(meta), o(out) {}
  std::map<Expr, std::string> vars;
  std::string val(const std::string& rhs)
  {
    std::string n = "v" + std::to_string(next++);
    o << "let " << n << " = " << rhs << ";\n";
    return n;
  }
  std::string ctor(const std::string& name)
  {
    if (!m.d_constructors.count(name)) { EO_FATAL() << "rust-meta: unknown constructor " << name; }
    return "Constructor::" + ident(name);
  }
  std::string args(const Expr& t, size_t start, const std::string& sep = ", ")
  {
    std::string ret;
    for (size_t i = start; i < t.getNumChildren(); ++i)
    {
      std::string v = expr(t[i]);
      ret += (i == start ? "" : sep) + v;
    }
    return ret;
  }
  std::string conditional(const Expr& c, const Expr& yes, const Expr& no, bool native)
  {
    std::string cv = expr(c);
    std::string n = "v" + std::to_string(next++);
    o << "let " << n << " = match s.boolean_value(" << cv << ", " << (native ? "true" : "false") << ")? {\nSome(true) => {\n";
    std::string a = expr(yes);
    o << a << "\n}, Some(false) => {\n";
    std::string b = expr(no);
    o << b << "\n}, None => s.stuck(),\n};\n";
    return n;
  }
  std::string op(Kind k, const Expr& t, size_t start)
  {
    if (k == Kind::EVAL_HASH) { EO_FATAL() << "rust-meta: eo::hash has no Logos specification"; }
    if (k == Kind::EVAL_IF_THEN_ELSE) { return conditional(t[start], t[start + 1], t[start + 2], false); }
    if (k == Kind::EVAL_REQUIRES)
    {
      std::string a = expr(t[start]), b = expr(t[start + 1]);
      std::string n = "v" + std::to_string(next++);
      o << "let " << n << " = if " << a << " == " << b << " && !s.is_stuck(" << a << ")? {\n";
      std::string r = expr(t[start + 2]);
      o << r << "\n} else { s.stuck() };\n";
      return n;
    }
    std::string as = args(t, start);
    if (k == Kind::EVAL_TYPE_OF || k == Kind::EVAL_NIL || k == Kind::EVAL_DT_CONSTRUCTORS || k == Kind::EVAL_DT_SELECTORS)
    {
      return val(ident("$eo_" + kindToTerm(k).substr(4)) + "(s, " + as + ")?");
    }
    // Match by EO name, so the C++ and Rust enum declaration orders are
    // independent. The generated runtime validates arities itself.
    return val("s.operator(" + quote(kindToTerm(k).substr(4)) + ", &[" + as + "])?");
  }
  std::string expr(const Expr& t)
  {
    auto var = vars.find(t);
    if (var != vars.end()) { return var->second; }
    Kind k = t.getKind();
    if (isLiteral(k)) { return val("s.literal(" + literal(t) + ")?"); }
    if (t.getNumChildren() == 0)
    {
      if (k == Kind::PARAM) { EO_FATAL() << "rust-meta: unbound parameter " << t; }
      if (k == Kind::PROGRAM_CONST) { return val(ident(getName(t)) + "(s)?"); }
      std::string n = k == Kind::TYPE ? "$emb_Type" : k == Kind::BOOL_TYPE ? "$emb_Bool" : getName(t);
      return val("s.construct(" + ctor(n) + ", &[])?");
    }
    if (k == Kind::APPLY_OPAQUE)
    {
      std::string n = getName(t[0]);
      if (starts(n, "$native_apply_"))
      {
        std::string name = getName(t[1]);
        if (name == "ite" && t.getNumChildren() == 5) { return conditional(t[2], t[3], t[4], true); }
        std::string as = args(t, 2);
        return val("s.native(" + quote(name) + ", &[" + as + "])?");
      }
      std::string as = args(t, 1);
      return val("s.construct(" + ctor(n) + ", &[" + as + "])?");
    }
    if (k == Kind::APPLY && t[0].getKind() == Kind::PROGRAM_CONST)
    {
      std::string n = getName(t[0]);
      Kind b = builtin(n);
      if (b != Kind::NONE) { return op(b, t, 1); }
      std::string as = args(t, 1);
      return val(ident(n) + "(s" + (as.empty() ? "" : ", " + as) + ")?");
    }
    if (isLiteralOp(k)) { return op(k, t, 0); }
    if (k == Kind::FUNCTION_TYPE)
    {
      size_t n = t.getNumChildren();
      std::string tail = expr(t[n - 1]);
      for (size_t i = n - 1; i > 0; --i)
      {
        std::string a = expr(t[i - 1]);
        std::string h = val("s.named(\"$emb_FunType\", &[])?");
        std::string f = val("s.apply(" + h + ", " + a + ")?");
        tail = val("s.apply(" + f + ", " + tail + ")?");
      }
      return tail;
    }
    if (k == Kind::APPLY && t.getNumChildren() == 2)
    {
      std::string f = expr(t[0]), a = expr(t[1]);
      return val("s.apply(" + f + ", " + a + ")?");
    }
    if (k == Kind::VARIABLE)
    {
      std::string as = args(t, 0);
      return val("s.named(\"$emb_Var\", &[" + as + "])?");
    }
    EO_FATAL() << "rust-meta: unsupported expression " << t << " (" << k << ")";
    return "";
  }
  void pattern(const Expr& t, const std::string& value, size_t c)
  {
    const std::string fail = " { break 'case" + std::to_string(c) + "; }\n";
    Kind k = t.getKind();
    if (k == Kind::PARAM)
    {
      auto it = vars.find(t);
      if (it != vars.end()) { o << "if " << value << " != " << it->second << fail; }
      else { vars[t] = value; }
      return;
    }
    if (k == Kind::FUNCTION_TYPE && t.getNumChildren() == 2)
    {
      std::string fields = val("s.unapply(" + value + ")?");
      o << "let Some((f, r)) = " << fields << " else" << fail << ";\n";
      std::string r = val("r");
      std::string f = val("s.unapply(f)?");
      o << "let Some((op, l)) = " << f << " else" << fail << ";\n"
        << "if !s.is_named(op, \"$emb_FunType\")?" << fail;
      std::string l = val("l");
      pattern(t[0], l, c);
      pattern(t[1], r, c);
      return;
    }
    if (k == Kind::APPLY && t.getNumChildren() == 2)
    {
      std::string fields = val("s.unapply(" + value + ")?");
      o << "let Some((f, a)) = " << fields << " else" << fail << ";\n";
      std::string f = val("f"), a = val("a");
      pattern(t[0], f, c);
      pattern(t[1], a, c);
      return;
    }
    if (k == Kind::APPLY_OPAQUE || k == Kind::VARIABLE)
    {
      size_t start = k == Kind::VARIABLE ? 0 : 1;
      std::string n = k == Kind::VARIABLE ? "$emb_Var" : getName(t[0]);
      std::string fields;
      if (starts(n, "$native_apply_"))
      {
        fields = val("s.native_pattern(" + quote(getName(t[1])) + ", " + value + ")?");
        start = 2;
      }
      else { fields = val("s.destruct(" + ctor(n) + ", " + value + ")?"); }
      o << "let Some(fields) = " << fields << " else" << fail << ";\n";
      fields = val("fields");
      for (size_t i = start; i < t.getNumChildren(); ++i)
      {
        pattern(t[i], fields + "[" + std::to_string(i - start) + "]", c);
      }
      return;
    }
    if (isLiteral(k) || t.getNumChildren() == 0)
    {
      std::string expected = expr(t);
      o << "if " << value << " != " << expected << fail;
      return;
    }
    EO_FATAL() << "rust-meta: unsupported pattern " << t;
  }

 private:
  RustMetaReduce& m;
  std::ostream& o;
  size_t next = 0;
};

std::string RustMetaReduce::emitProgram(const std::string& name, const Program& p)
{
  std::ostringstream out;
  Emitter e(*this, out);
  bool cases = p.body.getKind() == Kind::PROGRAM;
  Expr ty = cases ? p.symbol.getType() : Expr();
  size_t nargs = cases ? ty.getNumChildren() - 1 : 0;
  out << "// EO program " << quote(name) << "\npub fn " << ident(name) << "(s: &mut Store";
  for (size_t i = 0; i < nargs; ++i) { out << ", a" << i << ": Term"; }
  out << ") -> CheckResult<Term> {\ns.enter()?;\nlet result = (|| {\n";
  if (cases && !p.isDefine)
  {
    std::vector<MetaKind> kinds;
    bool checker = false;
    for (size_t i = 0; i < ty.getNumChildren(); ++i)
    {
      kinds.push_back(getTypeMetaKindFor(ty[i], MetaKind::EUNOIA, true));
      checker |= isCheckerMetaKind(kinds.back());
    }
    if (!checker && kinds.back() == MetaKind::EUNOIA)
    {
      std::string test;
      for (size_t i = 0; i < nargs; ++i)
      {
        if (kinds[i] == MetaKind::EUNOIA) { test += (test.empty() ? "" : " || ") + std::string("s.is_stuck(a") + std::to_string(i) + ")?"; }
      }
      if (!test.empty()) { out << "if " << test << " { return Ok(s.stuck()); }\n"; }
    }
  }
  if (cases)
  {
    for (size_t c = 0; c < p.body.getNumChildren(); ++c)
    {
      Expr pat = p.body[c][0];
      if (pat.getNumChildren() != nargs + 1) { EO_FATAL() << "rust-meta: bad pattern arity for " << name; }
      out << "'case" << c << ": {\n";
      e.vars.clear();
      for (size_t j = 0; j < nargs; ++j) { e.pattern(pat[j + 1], "a" + std::to_string(j), c); }
      std::string v = e.expr(p.body[c][1]);
      out << "return Ok(" << v << ");\n}\n";
    }
    out << "Ok(s.stuck())\n";
  }
  else { std::string v = e.expr(p.body); out << "Ok(" << v << ")\n"; }
  out << "})();\ns.leave();\nresult\n}\n";
  return out.str();
}

void RustMetaReduce::output(const std::string& file, const std::string& text) const
{
  std::string path = getOutputPath("plugins/rust_meta/checker/" + file);
  std::ofstream out(path);
  if (!out || !(out << text)) { EO_FATAL() << "rust-meta: cannot write " << path; }
}

void RustMetaReduce::finalize()
{
  if (!d_programs.count("$eo_checker_is_refutation"))
  {
    EO_FATAL() << "rust-meta: expected structural desugar output including the whole checker";
  }
  auto names = reachable();
  std::ostringstream code, manifest;
  code << "use crate::*;\n";
  manifest << "source\trust\n";
  // Complete generation before opening outputs, so unsupported constructs
  // cannot leave behind a partially generated checker.
  for (const auto& n : names)
  {
    code << emitProgram(n, d_programs.at(n));
    manifest << n << '\t' << ident(n) << '\n';
  }
  std::string lib = read(getResourcePath("plugins/rust_meta/runtime/lib.rs.in"));
  for (const char* n : {"$eo_typeof", "$eo_nil", "$eo_is_list_nil", "$eo_checker_is_refutation"})
  {
    lib = replace_all(lib, "@" + std::string(n) + "@", ident(n));
  }
  output("src/lib.rs", lib);
  output("src/generated.rs", code.str());
  output("src/schema.rs", schema());
  output("functions.tsv", manifest.str());
  for (const char* file : {"num.rs", "eostring.rs", "bitvec.rs", "lit.rs", "kind.rs", "codec.rs"})
  {
    output(std::string("src/") + file, read(getResourcePath(std::string("plugins/rust_meta/runtime/") + file)));
  }
  output("Cargo.toml", read(getResourcePath("plugins/rust_meta/runtime/Cargo.toml.in")));
  output("LICENSE.pathos", read(getResourcePath("plugins/rust_meta/runtime/LICENSE.pathos")));
}

}  // namespace ethos
