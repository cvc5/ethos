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
  if (!in)
  {
    EO_FATAL() << "rust-meta: cannot read " << path;
  }
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
        || (c >= '0' && c <= '9'))
    {
      out << c;
    }
    else
    {
      out << '_' << std::hex << std::setw(2) << std::setfill('0')
          << unsigned(c);
    }
  }
  return out.str();
}

std::string RustMetaReduce::quote(const std::string& text)
{
  std::ostringstream out;
  out << '"';
  for (unsigned char c : text)
  {
    if (c == '"' || c == '\\')
    {
      out << '\\' << c;
    }
    else if (c < 32 || c == 127)
    {
      out << "\\u{" << std::hex << unsigned(c) << std::dec << '}';
    }
    else
    {
      // Rust source is UTF-8, so multi-byte sequences pass through unchanged.
      out << c;
    }
  }
  out << '"';
  return out.str();
}

Kind RustMetaReduce::builtin(const std::string& name)
{
  // Signature-dependent metadata is compiled, including typeof and nil.
  if (!starts(name, "$eo_"))
  {
    return Kind::NONE;
  }
  for (int i = int(Kind::EVAL_IS_OK); i <= int(Kind::EVAL_DT_SELECTORS); ++i)
  {
    Kind k = static_cast<Kind>(i);
    if (k == Kind::EVAL_TYPE_OF || k == Kind::EVAL_NIL
        || k == Kind::EVAL_DT_CONSTRUCTORS || k == Kind::EVAL_DT_SELECTORS)
    {
      continue;
    }
    if (kindToTerm(k) == "eo::" + name.substr(4))
    {
      return k;
    }
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
  if (starts(name, "$native_") || !beginFinalizeDecl(e))
  {
    return;
  }
  Expr ty = e.getType();
  size_t arity = d_state.getAttributeKind(e.getValue()) == Attr::OPAQUE
                     ? ty.getNumChildren() - 1
                     : 0;
  d_constructorOrder.push_back(name);
  d_constructors.emplace(name, Constructor{arity});
}

void RustMetaReduce::defineProgram(const Expr& v, const Expr& prog)
{
  if (!prog.isNull())
  {
    d_programs[getName(v)] = {v, prog, false};
  }
}

void RustMetaReduce::define(const std::string& name, const Expr& e)
{
  if (!starts(name, "$eo_") || !getEmbedTypeApp(e).isNull())
  {
    return;
  }
  Expr symbol, prog;
  if (buildLambdaDefineProgram(name, e, symbol, prog))
  {
    d_programs[name] = {symbol, prog, true};
  }
  else
  {
    d_programs[name] = {e, e, true};
  }
}

bool RustMetaReduce::echo(const std::string& msg)
{
  if (starts(msg, "lean-parser-op "))
  {
    std::istringstream in(msg.substr(15));
    std::string surface, name, arity, index, attr;
    if (in >> surface >> name >> arity >> index >> attr
        && starts(attr, "left-assoc"))
    {
      d_leftAssoc.insert(name);
    }
  }
  return false;
}

std::set<std::string> RustMetaReduce::reachable() const
{
  const std::set<std::string> roots{"$eo_checker_is_refutation",
                                    "$eo_invoke_cmd_list",
                                    "$eo_invoke_assume_list",
                                    "$eo_state_is_refutation",
                                    "$eo_typeof",
                                    "$eo_nil",
                                    "$eo_is_list_nil",
                                    "$eo_dt_constructors",
                                    "$eo_dt_selectors",
                                    "$eo_to_smt",
                                    "$eo_to_smt_type",
                                    "$smtx_typeof",
                                    "$smtx_type_wf",
                                    "$smtx_type_wf_component"};
  std::vector<std::string> todo;
  for (const auto& p : d_programs)
  {
    if (starts(p.first, "$eo_prog_") || roots.count(p.first))
    {
      todo.push_back(p.first);
    }
  }
  std::set<std::string> seen;
  while (!todo.empty())
  {
    std::string name = todo.back();
    todo.pop_back();
    if (builtin(name) != Kind::NONE || !seen.insert(name).second)
    {
      continue;
    }
    auto p = d_programs.find(name);
    if (p == d_programs.end())
    {
      EO_FATAL() << "rust-meta: undefined reachable program " << name;
    }
    std::vector<Expr> terms{p->second.body};
    std::set<Expr> visited;
    while (!terms.empty())
    {
      Expr e = terms.back();
      terms.pop_back();
      if (!visited.insert(e).second)
      {
        continue;
      }
      if (e.getKind() == Kind::PROGRAM_CONST)
      {
        todo.push_back(getName(e));
      }
      for (size_t i = 0; i < e.getNumChildren(); ++i)
      {
        terms.push_back(e[i]);
      }
    }
  }
  return seen;
}

void RustMetaReduce::selectCaches(const std::set<std::string>& names)
{
  // Only bodies contribute call edges. A case's pattern is headed by its
  // owning program too, but that is not a recursive call.
  std::map<std::string, std::set<std::string>> calls;
  size_t id = 0;
  for (const std::string& name : names)
  {
    d_programIds[name] = id++;
    d_cacheKinds[name] = CacheKind::NONE;
    const Expr& body = d_programs.at(name).body;
    std::vector<Expr> todo;
    if (body.getKind() == Kind::PROGRAM)
    {
      for (size_t i = 0; i < body.getNumChildren(); ++i)
      {
        todo.push_back(body[i][1]);
      }
    }
    else
    {
      todo.push_back(body);
    }
    std::set<Expr> visited;
    while (!todo.empty())
    {
      Expr term = todo.back();
      todo.pop_back();
      if (!visited.insert(term).second)
      {
        continue;
      }
      std::string callee;
      Kind operation = term.getKind();
      if (term.getKind() == Kind::PROGRAM_CONST)
      {
        callee = getName(term);
        operation = builtin(callee);
      }
      else if (term.getKind() == Kind::EVAL_TYPE_OF)
      {
        callee = "$eo_typeof";
      }
      else if (term.getKind() == Kind::EVAL_NIL)
      {
        callee = "$eo_nil";
      }
      else if (term.getKind() == Kind::EVAL_DT_CONSTRUCTORS)
      {
        callee = "$eo_dt_constructors";
      }
      else if (term.getKind() == Kind::EVAL_DT_SELECTORS)
      {
        callee = "$eo_dt_selectors";
      }
      if (names.count(callee))
      {
        calls[name].insert(callee);
      }
      // Native list operations consult compiled signature metadata too.
      if (isListLiteralOp(operation))
      {
        for (const char* metadata :
             {"$eo_typeof", "$eo_nil", "$eo_is_list_nil"})
        {
          if (names.count(metadata))
          {
            calls[name].insert(metadata);
          }
        }
      }
      for (size_t i = 0; i < term.getNumChildren(); ++i)
      {
        todo.push_back(term[i]);
      }
    }
  }
  for (const std::string& name : names)
  {
    const Program& program = d_programs.at(name);
    if (program.body.getKind() != Kind::PROGRAM || program.isDefine)
    {
      continue;
    }
    Expr type = program.symbol.getType();
    if ((name == "$eo_typeof" || name == "$smtx_typeof")
        && type.getNumChildren() == 2)
    {
      d_cacheKinds[name] =
          name == "$eo_typeof" ? CacheKind::EO_TYPE : CacheKind::SMT_TYPE;
      continue;
    }
    bool termArgument = false, checker = false;
    for (size_t i = 0; i < type.getNumChildren(); ++i)
    {
      MetaKind kind = getTypeMetaKindFor(type[i], MetaKind::EUNOIA, true);
      checker |= isCheckerMetaKind(kind);
      if (i + 1 < type.getNumChildren() && kind != MetaKind::SMT_BUILTIN
          && kind != MetaKind::PROOF)
      {
        termArgument = true;
      }
    }
    if (!termArgument || checker)
    {
      continue;
    }
    // Membership in a call-graph cycle includes mutual recursion. Keeping
    // tiny nonrecursive helpers out avoids a lookup on every generated call.
    std::set<std::string> visited;
    std::vector<std::string> todo(calls[name].begin(), calls[name].end());
    while (!todo.empty())
    {
      std::string callee = todo.back();
      todo.pop_back();
      if (callee == name)
      {
        d_cacheKinds[name] = CacheKind::PROGRAM;
        break;
      }
      if (!visited.insert(callee).second)
      {
        continue;
      }
      for (const std::string& next : calls[callee])
      {
        todo.push_back(next);
      }
    }
  }
}

bool RustMetaReduce::isUserConstructor(const std::string& name)
{
  return !starts(name, "$emb_") && !starts(name, "$eo_")
         && !starts(name, "$smt_");
}

std::string RustMetaReduce::schema() const
{
  std::ostringstream out;
  out << "use crate::Embedding;\n#[derive(Copy, Clone, Debug, PartialEq, Eq, "
         "Hash, PartialOrd, Ord)]\npub enum Constructor {\n";
  for (const auto& c : d_constructors)
  {
    out << ident(c.first) << ",\n";
  }
  out << "}\nimpl Constructor {\npub fn is_user(self) -> bool { match self "
         "{\n";
  for (const auto& c : d_constructors)
  {
    if (isUserConstructor(c.first))
    {
      out << "Self::" << ident(c.first) << " => true,\n";
    }
  }
  out << "_ => false, }}\npub fn arity(self) -> usize { match self {\n";
  for (const auto& c : d_constructors)
  {
    out << "Self::" << ident(c.first) << " => " << c.second.arity << ",\n";
  }
  out << "}}\npub fn is_left_assoc(self) -> bool { match self {\n";
  for (const auto& n : d_leftAssoc)
  {
    if (d_constructors.count(n) != 0)
    {
      out << "Self::" << ident(n) << " => true,\n";
    }
  }
  out << "_ => false, }}\npub fn order_key(self) -> (usize, usize) { match "
         "self {\n";
  std::map<std::string, size_t> tags;
  size_t next = 0;
  const std::set<std::string> metaTypes{
      "$eo_Term", "$eo_Rule", "$eo_Cmd", "$eo_Proof", "$eo_pf"};
  for (const std::string& name : d_constructorOrder)
  {
    if ((starts(name, "$emb_") && name.find('.') == std::string::npos)
        || (starts(name, "$eo_") && !metaTypes.count(name)))
    {
      tags[name] = next++;
    }
  }
  // Users without a wrapper sort after every $eo_Term constructor. Remaining
  // constructors (datatype constructors, meta types) take fresh tags after
  // that, so tags are unique across datatypes while keeping each datatype's
  // declaration order.
  const size_t unwrappedUser = next++;
  std::map<size_t, size_t> users;
  for (const std::string& name : d_constructorOrder)
  {
    size_t arity = d_constructors.at(name).arity;
    size_t tag, subtag = 0;
    if (tags.count(name))
    {
      tag = tags.at(name);
    }
    else if (isUserConstructor(name))
    {
      std::string wrapper =
          "$emb_UOp" + (arity == 0 ? "" : std::to_string(arity));
      tag = tags.count(wrapper) ? tags.at(wrapper) : unwrappedUser;
      subtag = users[arity]++;
    }
    else
    {
      tag = next++;
    }
    out << "Self::" << ident(name) << " => (" << tag << ", " << subtag
        << "),\n";
  }
  // How the runtime represents what each constructor builds, decided here
  // from the constructor's name in the embedding of terms, so that the
  // runtime compares no names.
  static const std::vector<std::pair<std::string, std::string>> embeddings{
      {"$emb_Stuck", "Stuck"},
      {"$emb_Apply", "Apply"},
      {"$emb_Boolean", "Boolean"},
      {"$emb_Numeral", "Numeral"},
      {"$emb_Rational", "Rational"},
      {"$emb_String", "String"},
      {"$emb_Binary", "Binary"},
      {"$emb_Var", "Var"}};
  out << "}}\npub fn embedding(self) -> Embedding { match self {\n";
  for (const auto& c : d_constructors)
  {
    std::string embedding = starts(c.first, "$emb_UOp") ? "UOp" : "";
    for (const auto& e : embeddings)
    {
      if (c.first == e.first)
      {
        embedding = e.second;
      }
    }
    if (!embedding.empty())
    {
      out << "Self::" << ident(c.first) << " => Embedding::" << embedding
          << ",\n";
    }
  }
  out << "_ => Embedding::Data, }}\n"
         "/// The constructor of an embedding that has exactly one.\n"
         "pub fn of_embedding(e: Embedding) -> Option<Self> { match e {\n";
  for (const auto& e : embeddings)
  {
    if (d_constructors.count(e.first) != 0)
    {
      out << "Embedding::" << e.second << " => Some(Self::" << ident(e.first)
          << "),\n";
    }
  }
  out << "_ => None, }}\n}\n";
  return out.str();
}

std::string RustMetaReduce::constructorNames() const
{
  std::ostringstream out;
  out << "//! The constructors by name.\nuse crate::Constructor;\n"
         "impl Constructor {\npub fn name(self) -> &'static str { match "
         "self {\n";
  for (const auto& c : d_constructors)
  {
    out << "Self::" << ident(c.first) << " => " << quote(c.first) << ",\n";
  }
  out << "}}\npub fn from_name(name: &str) -> Option<Self> { Some(match name "
         "{\n";
  for (const auto& c : d_constructors)
  {
    out << quote(c.first) << " => Self::" << ident(c.first) << ",\n";
  }
  out << "_ => return None, }) }\n}\n";
  return out.str();
}

std::string RustMetaReduce::constructorOption(const std::string& name) const
{
  return d_constructors.count(name) != 0
             ? "Some(Constructor::" + ident(name) + ")"
             : "None";
}

std::string RustMetaReduce::expandConstructors(std::string text) const
{
  // "@ctor:NAME@" in a runtime template is the constructor of that name, as
  // an Option: None where the signature has none.
  const std::string open = "@ctor:";
  size_t at;
  while ((at = text.find(open)) != std::string::npos)
  {
    size_t end = text.find('@', at + open.size());
    if (end == std::string::npos)
    {
      EO_FATAL() << "rust-meta: unterminated @ctor: in a runtime template";
    }
    std::string name = text.substr(at + open.size(), end - at - open.size());
    text.replace(at, end + 1 - at, constructorOption(name));
  }
  return text;
}

std::string RustMetaReduce::literal(const Expr& e)
{
  const Literal* l = e.getValue()->asLiteral();
  std::ostringstream out;
  switch (e.getKind())
  {
    case Kind::BOOLEAN:
      return l->d_bool ? "Lit::Bool(true)" : "Lit::Bool(false)";
    case Kind::NUMERAL:
      return "Lit::Numeral(parse_int(" + quote(l->d_int.toString()) + ")?)";
    case Kind::RATIONAL:
    case Kind::DECIMAL:
      return "Lit::Rational(parse_rat(" + quote(l->d_rat.toString()) + ")?)";
    case Kind::BINARY:
    case Kind::HEXADECIMAL:
      out << "Lit::Binary(BitVec::new(" << l->d_bv.getSize() << ", &parse_int("
          << quote(l->d_bv.getValue().toString()) << ")?))";
      return out.str();
    case Kind::STRING:
      out << "Lit::String(EoString::from_code_points(vec![";
      for (unsigned c : l->d_str.getVec())
      {
        out << c << ',';
      }
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
    if (!m.d_constructors.count(name))
    {
      EO_FATAL() << "rust-meta: unknown constructor " << name;
    }
    return "Constructor::" + ident(name);
  }
  /** The runtime's `EvalOp` of a kind: `EVAL_IS_OK` is `IsOk`. */
  static std::string evalOp(Kind k)
  {
    std::ostringstream name;
    name << k;
    std::string ret;
    bool upper = true;
    for (char c : name.str().substr(5))
    {
      if (c == '_')
      {
        upper = true;
        continue;
      }
      ret += upper ? c : static_cast<char>(std::tolower(c));
      upper = false;
    }
    return ret;
  }
  /**
   * A call of a native operation. The runtime names its operations by an
   * enum (NativeOp in runtime/native.rs); a name it does not have, or a
   * number of arguments the operation does not take, is the runtime's
   * UnsupportedNative error, as when the runtime compared the names.
   */
  std::string native(const std::string& name,
                     size_t nargs,
                     const std::string& as)
  {
    static const std::map<std::string, std::pair<std::string, size_t>> ops{
        {"teq", {"Teq", 2}},
        {"Teq", {"Teq", 2}},
        {"tcmp", {"Tcmp", 2}},
        {"is_ok", {"IsOk", 1}},
        {"not", {"Not", 1}},
        {"and", {"And", 2}},
        {"or", {"Or", 2}},
        {"iff", {"Iff", 2}},
        {"nat.succ", {"NatSucc", 1}},
        {"nat.pred", {"NatPred", 1}},
        {"nat.to_int", {"NatToInt", 1}},
        {"Int.ofNat", {"NatToInt", 1}},
        {"int.to_nat", {"IntToNat", 1}},
        {"Int.toNat", {"IntToNat", 1}},
        {"zeq", {"Zeq", 2}},
        {"nateq", {"Nateq", 2}},
        {"zlt", {"Zlt", 2}},
        {"zleq", {"Zleq", 2}},
        {"nat.lt", {"NatLt", 2}},
        {"zplus", {"Zplus", 2}},
        {"zmult", {"Zmult", 2}},
        {"zdiv_total", {"ZdivTotal", 2}},
        {"div_total", {"DivTotal", 2}},
        {"mod_total", {"ModTotal", 2}},
        {"zmod_total", {"ZmodTotal", 2}},
        {"zexp_total", {"ZexpTotal", 2}},
        {"binary_and", {"BinaryAnd", 2}},
        {"binary_or", {"BinaryOr", 2}},
        {"binary_xor", {"BinaryXor", 2}},
        {"zneg", {"Zneg", 1}},
        {"zabs", {"Zabs", 1}},
        {"qeq", {"Qeq", 2}},
        {"qlt", {"Qlt", 2}},
        {"qleq", {"Qleq", 2}},
        {"qplus", {"Qplus", 2}},
        {"qmult", {"Qmult", 2}},
        {"qdiv_total", {"QdivTotal", 2}},
        {"qneg", {"Qneg", 1}},
        {"qabs", {"Qabs", 1}},
        {"mk_rational", {"MkRational", 2}},
        {"to_int", {"ToInt", 1}},
        {"to_real", {"ToReal", 1}},
        {"streq", {"Streq", 2}},
        {"int.pow2", {"IntPow2", 1}},
        {"uconst_id", {"UconstId", 1}},
        {"const_id", {"ConstId", 1}},
        {"string_valid", {"StringValid", 1}},
        {"string_prefix_eq", {"StringPrefixEq", 2}}};
    if (nargs == 0)
    {
      // a constant
      if (name == "true" || name == "false")
      {
        return "s.native_bool(" + name + ")?";
      }
      if (name == "nat.zero")
      {
        return "s.native_nat_zero()?";
      }
      // a numeral or a string, which the runtime reads
      return "s.native_constant(" + quote(name) + ")?";
    }
    auto it = ops.find(name);
    if (it == ops.end() || it->second.second != nargs)
    {
      return "s.unsupported_native(" + quote(name) + ")?";
    }
    return "s.native_op(NativeOp::" + it->second.first + ", &[" + as + "])?";
  }
  /** A native constructor or constant as a pattern for `value`. */
  std::string nativePattern(const std::string& name, const std::string& value)
  {
    if (name == "nat.succ")
    {
      return "s.native_pattern_succ(" + value + ")?";
    }
    if (name == "true" || name == "false")
    {
      return "s.native_pattern_bool(" + name + ", " + value + ")?";
    }
    if (name == "nat.zero")
    {
      return "s.native_pattern_nat_zero(" + value + ")?";
    }
    return "s.native_pattern_constant(" + quote(name) + ", " + value + ")?";
  }
  /**
   * The term of the constructor `name` of the embedding, which a signature
   * may lack; without it, the runtime's InvalidConstructor error, as when
   * the runtime looked the name up.
   */
  std::string named(const std::string& name, const std::string& as)
  {
    if (m.d_constructors.count(name) == 0)
    {
      return "s.missing_constructor()?";
    }
    return "s.construct(Constructor::" + ident(name) + ", &[" + as + "])?";
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
  std::string conditional(const Expr& c,
                          const Expr& yes,
                          const Expr& no,
                          bool native)
  {
    std::string cv = expr(c);
    std::string n = "v" + std::to_string(next++);
    o << "let " << n << " = match s.boolean_value(" << cv << ", "
      << (native ? "true" : "false") << ")? {\nSome(true) => {\n";
    std::string a = expr(yes);
    o << a << "\n}, Some(false) => {\n";
    std::string b = expr(no);
    o << b << "\n}, None => s.stuck(),\n};\n";
    return n;
  }
  std::string op(Kind k, const Expr& t, size_t start)
  {
    if (k == Kind::EVAL_HASH)
    {
      EO_FATAL() << "rust-meta: eo::hash has no Logos specification";
    }
    if (k == Kind::EVAL_IF_THEN_ELSE)
    {
      return conditional(t[start], t[start + 1], t[start + 2], false);
    }
    if (k == Kind::EVAL_REQUIRES)
    {
      std::string a = expr(t[start]), b = expr(t[start + 1]);
      std::string n = "v" + std::to_string(next++);
      o << "let " << n << " = if " << a << " == " << b << " && !s.is_stuck("
        << a << ")? {\n";
      std::string r = expr(t[start + 2]);
      o << r << "\n} else { s.stuck() };\n";
      return n;
    }
    std::string as = args(t, start);
    if (k == Kind::EVAL_TYPE_OF || k == Kind::EVAL_NIL
        || k == Kind::EVAL_DT_CONSTRUCTORS || k == Kind::EVAL_DT_SELECTORS)
    {
      return val(ident("$eo_" + kindToTerm(k).substr(4)) + "(s, " + as + ")?");
    }
    // Name the runtime's operator, so the C++ and Rust enum declaration
    // orders are independent. The runtime validates arities itself.
    return val("s.builtin(EvalOp::" + evalOp(k) + ", &[" + as + "])?");
  }
  std::string expr(const Expr& t)
  {
    auto var = vars.find(t);
    if (var != vars.end())
    {
      return var->second;
    }
    Kind k = t.getKind();
    if (isLiteral(k))
    {
      return val("s.literal(" + literal(t) + ")?");
    }
    if (t.getNumChildren() == 0)
    {
      if (k == Kind::PARAM)
      {
        EO_FATAL() << "rust-meta: unbound parameter " << t;
      }
      if (k == Kind::PROGRAM_CONST)
      {
        return val(ident(getName(t)) + "(s)?");
      }
      std::string n = k == Kind::TYPE        ? "$emb_Type"
                      : k == Kind::BOOL_TYPE ? "$emb_Bool"
                                             : getName(t);
      return val("s.construct(" + ctor(n) + ", &[])?");
    }
    if (k == Kind::APPLY_OPAQUE)
    {
      std::string n = getName(t[0]);
      if (starts(n, "$native_apply_"))
      {
        std::string name = getName(t[1]);
        if (name == "ite" && t.getNumChildren() == 5)
        {
          return conditional(t[2], t[3], t[4], true);
        }
        std::string as = args(t, 2);
        return val(native(name, t.getNumChildren() - 2, as));
      }
      std::string as = args(t, 1);
      return val("s.construct(" + ctor(n) + ", &[" + as + "])?");
    }
    if (k == Kind::APPLY && t[0].getKind() == Kind::PROGRAM_CONST)
    {
      std::string n = getName(t[0]);
      Kind b = builtin(n);
      if (b != Kind::NONE)
      {
        return op(b, t, 1);
      }
      std::string as = args(t, 1);
      return val(ident(n) + "(s" + (as.empty() ? "" : ", " + as) + ")?");
    }
    if (isLiteralOp(k))
    {
      return op(k, t, 0);
    }
    if (k == Kind::FUNCTION_TYPE)
    {
      size_t n = t.getNumChildren();
      std::string tail = expr(t[n - 1]);
      for (size_t i = n - 1; i > 0; --i)
      {
        std::string a = expr(t[i - 1]);
        std::string h = val(named("$emb_FunType", ""));
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
      return val(named("$emb_Var", as));
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
      if (it != vars.end())
      {
        o << "if " << value << " != " << it->second << fail;
      }
      else
      {
        vars[t] = value;
      }
      return;
    }
    if (k == Kind::FUNCTION_TYPE && t.getNumChildren() == 2)
    {
      std::string fields = val("s.unapply(" + value + ")?");
      o << "let Some((f, r)) = " << fields << " else" << fail << ";\n";
      std::string r = val("r");
      std::string f = val("s.unapply(f)?");
      o << "let Some((op, l)) = " << f << " else" << fail << ";\n"
        << "if !s.is_node(op, " << m.constructorOption("$emb_FunType")
        << ")?" << fail;
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
        fields = val(nativePattern(getName(t[1]), value));
        start = 2;
      }
      else
      {
        fields = val("s.destruct(" + ctor(n) + ", " + value + ")?");
      }
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

std::string RustMetaReduce::emitProgram(const std::string& name,
                                        const Program& p)
{
  std::ostringstream out;
  Emitter e(*this, out);
  bool cases = p.body.getKind() == Kind::PROGRAM;
  Expr ty = cases ? p.symbol.getType() : Expr();
  size_t nargs = cases ? ty.getNumChildren() - 1 : 0;
  auto tailCall = [&](const Expr& body) {
    return body.getKind() == Kind::APPLY && body.getNumChildren() == nargs + 1
           && body[0] == p.symbol;
  };
  bool loop = false;
  if (cases)
  {
    for (size_t i = 0; i < p.body.getNumChildren(); ++i)
    {
      loop |= tailCall(p.body[i][1]);
    }
  }
  // The checking loop's premise lookup walks the state list one element at
  // a time, creating and interning a native numeral at each one. Where the
  // loop's constructors are the expected ones, it is compiled to the
  // runtime's Store::state_proven_nth, which gives the same results with a
  // machine counter (see its documentation in runtime/lib.rs.in).
  if (name == "$eo_state_proven_nth" && cases && nargs == 2
      && d_cacheKinds.at(name) == CacheKind::NONE
      && d_constructors.count("$emb_s.cons") > 0
      && d_programs.count("$eo_StateObj_proven") > 0)
  {
    out << "// EO program " << quote(name)
        << ", compiled to Store::state_proven_nth\npub fn " << ident(name)
        << "(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {\n"
        << "s.enter()?;\nlet result = s.state_proven_nth(Constructor::"
        << ident("$emb_s.cons") << ", a0, a1, " << ident("$eo_StateObj_proven")
        << ");\ns.leave();\nresult\n}\n";
    return out.str();
  }
  // Recognize the checking loop's guarded right fold, rather than relying
  // on its name alone. Check guards in source order and save their results;
  // unwind the pending pushes in reverse order, just as the recursive EO
  // definition does. Logos's invoke_assume_list_eq_fold (Cpc/ApiChecks.lean)
  // is the corresponding refinement statement for well-formed input lists.
  if (name == "$eo_invoke_assume_list" && cases && !p.isDefine && nargs == 2
      && p.body.getNumChildren() == 2
      && d_cacheKinds.at(name) == CacheKind::NONE)
  {
    Expr base = p.body[0][0], step = p.body[1][0], body = p.body[1][1];
    if (base.getNumChildren() == 3 && step.getNumChildren() == 3
        && base[1].getKind() == Kind::PARAM && p.body[0][1] == base[1]
        && base[2].getNumChildren() == 0 && getName(base[2]) == "$emb_al.nil"
        && step[1].getKind() == Kind::PARAM
        && step[2].getKind() == Kind::APPLY_OPAQUE
        && step[2].getNumChildren() == 3
        && getName(step[2][0]) == "$emb_al.cons"
        && step[2][1].getKind() == Kind::PARAM
        && step[2][2].getKind() == Kind::PARAM && body.getKind() == Kind::APPLY
        && body.getNumChildren() == 4
        && body[0].getKind() == Kind::PROGRAM_CONST
        && getName(body[0]) == "$eo_push_input_assume_check"
        && body[2] == step[2][1] && body[3].getKind() == Kind::APPLY
        && body[3].getNumChildren() == 3 && body[3][0] == p.symbol
        && body[3][1] == step[1] && body[3][2] == step[2][2])
    {
      out << "// EO program " << quote(name)
          << ", compiled to an iterative guarded fold\npub fn " << ident(name)
          << "(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {\n"
          << "s.enter()?;\nlet result = (|| {\n"
          << "let mut pending = Vec::new();\nlet mut args = a1;\n"
          << "let mut state = 'scan: loop {\n'case0: {\n";
      e.pattern(base[1], "a0", 0);
      e.pattern(base[2], "args", 0);
      out << "break 'scan a0;\n}\n'case1: {\n";
      e.vars.clear();
      e.pattern(step[1], "a0", 1);
      e.pattern(step[2], "args", 1);
      std::string guard = e.expr(body[1]), term = e.expr(body[2]);
      out << "pending.push((" << guard << ", " << term << "));\n";
      std::string tail = e.expr(body[3][2]);
      // One tick replaces each recursive enter, keeping the call budget
      // while making the depth independent of the number of assumptions.
      out << "args = " << tail << ";\ns.tick()?;\ncontinue 'scan;\n}\n"
          << "break 'scan s.stuck();\n};\n"
          << "while let Some((guard, term)) = pending.pop() {\n"
          << "state = " << ident(getName(body[0]))
          << "(s, guard, term, state)?;\n}\nOk(state)\n})();\n"
          << "s.leave();\nresult\n}\n";
      return out.str();
    }
  }
  out << "// EO program " << quote(name) << "\npub fn " << ident(name)
      << "(s: &mut Store";
  for (size_t i = 0; i < nargs; ++i)
  {
    out << (loop ? ", mut a" : ", a") << i << ": Term";
  }
  out << ") -> CheckResult<Term> {\ns.enter()?;\n";
  CacheKind cache = d_cacheKinds.at(name);
  std::string cachePut;
  if (cache != CacheKind::NONE)
  {
    // Tail-call loops overwrite a<i>; retain the original application key.
    out << "let cache_args = [";
    for (size_t i = 0; i < nargs; ++i)
    {
      out << (i == 0 ? "" : ", ") << "a" << i;
    }
    out << "];\n";
    std::string get;
    if (cache == CacheKind::PROGRAM)
    {
      std::string id =
          "ProgramId(" + std::to_string(d_programIds.at(name)) + ")";
      get = "s.cached_program(" + id + ", &cache_args)";
      cachePut = "s.cache_program(" + id + ", &cache_args, value)?;";
    }
    else
    {
      std::string kind = cache == CacheKind::EO_TYPE ? "TypeCacheKind::Eunoia"
                                                     : "TypeCacheKind::Smt";
      get = "s.cached_type(" + kind + ", cache_args[0])";
      cachePut = "s.cache_type(" + kind + ", cache_args[0], value)?;";
    }
    out << "match " << get << " {\n"
        << "Ok(Some(value)) => { s.leave(); return Ok(value); },\n"
        << "Ok(None) => {},\n"
        << "Err(error) => { s.leave(); return Err(error); },\n}\n";
  }
  out << "let result = (|| {\n";
  if (loop)
  {
    out << "'recur: loop {\ns.tick()?;\n";
  }
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
        if (kinds[i] == MetaKind::EUNOIA)
        {
          test += (test.empty() ? "" : " || ") + std::string("s.is_stuck(a")
                  + std::to_string(i) + ")?";
        }
      }
      if (!test.empty())
      {
        out << "if " << test << " { return Ok(s.stuck()); }\n";
      }
    }
  }
  std::ostringstream helpers;
  if (cases)
  {
    // Large sequential matches otherwise give every recursive invocation
    // one debug-build stack frame containing temporaries for every case.
    // Keep those temporaries in separate, small helpers. They do not enter
    // the evaluator again: budgets, caching and case order stay in this
    // function, and each helper implements exactly one source case.
    bool splitCases = p.body.getNumChildren() >= 8;
    Emitter helperEmitter(*this, helpers);
    std::string caseResult = "case_result_" + ident(name);
    std::string noMatch = loop ? caseResult + "::NoMatch" : "None";
    if (splitCases)
    {
      if (loop)
      {
        helpers << "#[allow(dead_code)]\nenum " << caseResult
                << " { NoMatch, Value(Term), Tail([Term; " << nargs << "]) }\n";
      }
      // One match result shared by all cases avoids a separate debug-build
      // result slot for every helper call in this recursive frame.
      out << "let mut case_index = 0_usize;\nwhile case_index < "
          << p.body.getNumChildren() << " {\n"
          << "let matched = match case_index {\n";
    }
    for (size_t c = 0; c < p.body.getNumChildren(); ++c)
    {
      Expr pat = p.body[c][0];
      if (pat.getNumChildren() != nargs + 1)
      {
        EO_FATAL() << "rust-meta: bad pattern arity for " << name;
      }
      Expr body = p.body[c][1];
      bool tail = loop && tailCall(body);
      std::ostream& co = splitCases ? helpers : out;
      Emitter& ce = splitCases ? helperEmitter : e;
      if (splitCases)
      {
        std::string helper = "case_" + std::to_string(c) + "_" + ident(name);
        helpers << "fn " << helper << "(s: &mut Store";
        out << c << " => " << helper << "(s";
        for (size_t j = 0; j < nargs; ++j)
        {
          helpers << ", a" << j << ": Term";
          out << ", a" << j;
        }
        helpers << ") -> CheckResult<" << (loop ? caseResult : "Option<Term>")
                << "> {\n";
        out << "),\n";
      }
      co << "'case" << c << ": {\n";
      ce.vars.clear();
      for (size_t j = 0; j < nargs; ++j)
      {
        ce.pattern(pat[j + 1], "a" + std::to_string(j), c);
      }
      if (tail)
      {
        std::vector<std::string> next;
        for (size_t j = 1; j <= nargs; ++j)
        {
          std::string value = ce.expr(body[j]);
          next.push_back(ce.val(value));
        }
        if (splitCases)
        {
          co << "return Ok(" << caseResult << "::Tail([";
          for (size_t j = 0; j < nargs; ++j)
          {
            co << (j == 0 ? "" : ", ") << next[j];
          }
          co << "]));\n}\n";
        }
        else
        {
          // Evaluate every argument before overwriting any of the inputs.
          for (size_t j = 0; j < nargs; ++j)
          {
            co << "a" << j << " = " << next[j] << ";\n";
          }
          co << "continue 'recur;\n}\n";
        }
      }
      else
      {
        std::string v = ce.expr(body);
        co << "return Ok("
           << (splitCases ? (loop ? caseResult + "::Value(" : "Some(") : "")
           << v << (splitCases ? ")" : "") << ");\n}\n";
      }
      if (splitCases)
      {
        helpers << "Ok(" << noMatch << ")\n}\n";
      }
    }
    if (splitCases)
    {
      out << "_ => Ok(" << noMatch << "),\n}?;\n";
      if (loop)
      {
        out << "match matched {\n"
            << caseResult << "::NoMatch => {},\n"
            << caseResult << "::Value(value) => return Ok(value),\n"
            << caseResult << "::Tail(next) => {\n";
        for (size_t j = 0; j < nargs; ++j)
        {
          out << "a" << j << " = next[" << j << "];\n";
        }
        out << "continue 'recur;\n}\n}\n";
      }
      else
      {
        out << "if let Some(value) = matched { return Ok(value); }\n";
      }
      out << "case_index += 1;\n}\n";
    }
    out << (loop ? "return Ok(s.stuck());\n}\n" : "Ok(s.stuck())\n");
  }
  else
  {
    std::string v = e.expr(p.body);
    out << "Ok(" << v << ")\n";
  }
  out << "})();\ns.leave();\n";
  if (!cachePut.empty())
  {
    out << "if let Ok(value) = result { " << cachePut << " }\n";
  }
  // Helpers are module items; emit them after closing the main function.
  out << "result\n}\n" << helpers.str();
  return out.str();
}

void RustMetaReduce::output(const std::string& file,
                            const std::string& text) const
{
  std::string path = getOutputPath("plugins/rust_meta/checker/" + file);
  std::ofstream out(path);
  if (!out || !(out << text))
  {
    EO_FATAL() << "rust-meta: cannot write " << path;
  }
}

void RustMetaReduce::finalize()
{
  // The runtime template and op() call these directly; require them here so
  // a bad input fails now rather than as a cargo build error.
  for (const char* n : {"$eo_checker_is_refutation",
                        "$eo_typeof",
                        "$eo_nil",
                        "$eo_is_list_nil",
                        "$eo_dt_constructors",
                        "$eo_dt_selectors"})
  {
    if (!d_programs.count(n))
    {
      EO_FATAL() << "rust-meta: expected structural desugar output including "
                    "the whole checker (missing "
                 << n << ")";
    }
  }
  auto names = reachable();
  selectCaches(names);
  std::ostringstream code, manifest;
  code << "use crate::*;\n";
  manifest << "source\trust\tlean_identifier\n";
  // Complete generation before opening outputs, so unsupported constructs
  // cannot leave behind a partially generated checker.
  for (const auto& n : names)
  {
    code << emitProgram(n, d_programs.at(n));
    std::string lean = replace_all(n, "-", "_");
    if (lean == "end" || lean == "variable")
    {
      lean = "__eo_" + lean;
    }
    else
    {
      for (const auto& replacement : std::vector<Replacement>{{"++", "concat"},
                                                              {"+", "plus"},
                                                              {"-", "neg"},
                                                              {"*", "mult"},
                                                              {"=>", "imp"},
                                                              {"<=", "leq"},
                                                              {"<", "lt"},
                                                              {">=", "geq"},
                                                              {">", "gt"},
                                                              {"=", "eq"},
                                                              {"/", "qdiv"},
                                                              {"^", "exp"},
                                                              {".", "_"},
                                                              {"@", "_at_"},
                                                              {"$", "__"}})
      {
        lean = replace_all(lean, replacement.first, replacement.second);
      }
    }
    manifest << n << '\t' << ident(n) << '\t' << lean << '\n';
  }
  std::string lib =
      read(getResourcePath("plugins/rust_meta/runtime/lib.rs.in"));
  for (const char* n : {"$eo_typeof",
                        "$eo_nil",
                        "$eo_is_list_nil",
                        "$eo_checker_is_refutation"})
  {
    lib = replace_all(lib, "@" + std::string(n) + "@", ident(n));
  }
  bool translation = true;
  for (const char* n : {"$eo_to_smt",
                        "$eo_to_smt_type",
                        "$smtx_typeof",
                        "$smtx_type_wf",
                        "$smtx_type_wf_component"})
  {
    translation &= names.count(n) != 0;
  }
  std::string checks =
      read(getResourcePath("plugins/rust_meta/runtime/translation.rs.in"));
  checks =
      replace_all(checks, "@HAS_TRANSLATION@", translation ? "true" : "false");
  const std::string unavailable =
      "let _ = t; Err(CheckError::UnsupportedNative(\"SMT translation is "
      "unavailable\"))";
  checks = replace_all(checks,
                       "@TRANSLATION_TYPE@",
                       translation ? "let t = generated::" + ident("$eo_to_smt")
                                         + "(self, t)?; generated::"
                                         + ident("$smtx_typeof") + "(self, t)"
                                   : unavailable);
  checks = replace_all(
      checks,
      "@TRANSLATION_SORT@",
      translation ? "generated::" + ident("$eo_to_smt_type") + "(self, t)"
                  : unavailable);
  checks = replace_all(
      checks,
      "@TRANSLATION_WF@",
      translation
          ? "let b = if component { generated::"
                + ident("$smtx_type_wf_component")
                + "(self, t)? } else { generated::" + ident("$smtx_type_wf")
                + "(self, t)? }; Ok(self.boolean_value(b, true)? == Some(true))"
          : "let _ = component; " + unavailable);
  std::istringstream masks(
      read(getResourcePath("plugins/rust_meta/cpc_translation_masks.txt")));
  std::ostringstream maskLengths, maskKinds;
  static const std::map<std::string, std::string> argKinds{
      {"term", "Term"},
      {"type", "Type"},
      {"wfTerm", "WfTerm"},
      {"wfElem", "WfElem"},
      {"list", "List"}};
  std::string line;
  while (std::getline(masks, line))
  {
    if (line.empty() || line[0] == '#')
    {
      continue;
    }
    std::istringstream words(line);
    std::string rule, kind;
    words >> rule;
    rule = "$emb_r." + rule;
    if (d_constructors.count(rule) == 0)
    {
      // not a rule of this signature
      continue;
    }
    size_t n = 0;
    maskKinds << "Constructor::" << ident(rule) << " => match i {\n";
    while (words >> kind)
    {
      auto it = argKinds.find(kind);
      maskKinds << n++ << " => Some(ArgKind::"
                << (it == argKinds.end() ? "Unknown" : it->second) << "),\n";
    }
    maskKinds << "_ => None,\n},\n";
    maskLengths << "Constructor::" << ident(rule) << " => Some(" << n
                << "),\n";
  }
  checks =
      replace_all(checks, "@TRANSLATION_MASK_LENGTHS@", maskLengths.str());
  checks = replace_all(checks, "@TRANSLATION_MASK_KINDS@", maskKinds.str());
  lib += checks;
  output("src/lib.rs", expandConstructors(lib));
  output("src/generated.rs", code.str());
  output("src/schema.rs", schema());
  output("src/names.rs", constructorNames());
  output("functions.tsv", manifest.str());
  std::ostringstream caches;
  caches << "source\tcache\tprogram_id\n";
  for (const auto& name : names)
  {
    CacheKind kind = d_cacheKinds.at(name);
    const char* policy = kind == CacheKind::EO_TYPE    ? "eo-type"
                         : kind == CacheKind::SMT_TYPE ? "smt-type"
                         : kind == CacheKind::PROGRAM  ? "program"
                                                       : "none";
    caches << name << '\t' << policy << '\t';
    if (kind == CacheKind::PROGRAM)
    {
      caches << d_programIds.at(name);
    }
    caches << '\n';
  }
  output("caches.tsv", caches.str());
  std::ostringstream constructors;
  constructors << "source\trust\tarity\n";
  for (const auto& c : d_constructors)
  {
    constructors << c.first << '\t' << ident(c.first) << '\t' << c.second.arity
                 << '\n';
  }
  output("constructors.tsv", constructors.str());
  for (const char* file : {"cache.rs",
                           "front.rs",
                           "native.rs",
                           "num.rs",
                           "eostring.rs",
                           "bitvec.rs",
                           "lit.rs",
                           "kind.rs",
                           "codec.rs"})
  {
    output(std::string("src/") + file,
           read(getResourcePath(std::string("plugins/rust_meta/runtime/")
                                + file)));
  }
  output("Cargo.toml",
         read(getResourcePath("plugins/rust_meta/runtime/Cargo.toml.in")));
  output("Cargo.lock",
         read(getResourcePath("plugins/rust_meta/runtime/Cargo.lock.in")));
  output("DEPENDENCIES.md",
         read(getResourcePath("plugins/rust_meta/runtime/DEPENDENCIES.md")));
  output("LICENSE.pathos",
         read(getResourcePath("plugins/rust_meta/runtime/LICENSE.pathos")));
}

}  // namespace ethos
