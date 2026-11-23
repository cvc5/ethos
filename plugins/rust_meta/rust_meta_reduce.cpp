/******************************************************************************
 * This file is part of the ethos project.
 * See COPYING for licensing information.
 ******************************************************************************/
#include "rust_meta_reduce.h"

#include <fstream>
#include <iomanip>
#include <memory>
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
/** `text` as a JSON string. */
std::string js(const std::string& text)
{
  std::ostringstream out;
  out << '"';
  for (unsigned char c : text)
  {
    if (c == '"' || c == '\\')
    {
      out << '\\' << c;
    }
    else if (c < 0x20)
    {
      out << "\\u" << std::hex << std::setw(4) << std::setfill('0')
          << unsigned(c) << std::dec;
    }
    else
    {
      out << c;
    }
  }
  out << '"';
  return out.str();
}
/** A list of strings as a JSON array. */
std::string jsList(const std::vector<std::string>& list)
{
  std::string ret = "[";
  for (size_t i = 0; i < list.size(); ++i)
  {
    ret += (i == 0 ? "" : ", ") + js(list[i]);
  }
  return ret + "]";
}
/**
 * A node of the trace of the generated code (see `d_trace` in the
 * header): what one call of the emitter's `expr` or `pattern` wrote. Its
 * fields are JSON text, in the order set; `sub` are the nodes of the
 * calls it made, in order; `helpers` the functions that the text it wrote
 * itself was cut into (see `close`).
 */
struct TraceNode
{
  std::vector<std::pair<std::string, std::string>> fields;
  std::vector<std::unique_ptr<TraceNode>> sub;
  std::vector<std::string> helpers;
  void set(const std::string& key, const std::string& json)
  {
    fields.emplace_back(key, json);
  }
  std::string json() const
  {
    std::string ret = "{";
    for (size_t i = 0; i < fields.size(); ++i)
    {
      ret += (i == 0 ? "" : ", ") + js(fields[i].first) + ": " + fields[i].second;
    }
    if (!helpers.empty())
    {
      ret += ", \"helpers\": " + jsList(helpers);
    }
    if (!sub.empty())
    {
      ret += ", \"sub\": [";
      for (size_t i = 0; i < sub.size(); ++i)
      {
        ret += (i == 0 ? "" : ", ") + sub[i]->json();
      }
      ret += "]";
    }
    return ret + "}";
  }
};
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
    // eo::max_code_point has no arguments and is no operator of the runtime,
    // see Emitter::expr.
    if (k == Kind::EVAL_TYPE_OF || k == Kind::EVAL_NIL
        || k == Kind::EVAL_DT_CONSTRUCTORS || k == Kind::EVAL_DT_SELECTORS
        || k == Kind::EVAL_MAX_CODE_POINT)
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

std::set<std::string> RustMetaReduce::reachable(
    const std::set<std::string>& without) const
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
    if ((starts(p.first, "$eo_prog_") || roots.count(p.first))
        && !without.count(p.first))
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
  out << "use crate::Embedding;\n#[derive(Copy, Clone)]\n"
         "pub enum Constructor {\n";
  for (const auto& c : d_constructors)
  {
    out << ident(c.first) << ",\n";
  }
  // Two constructors are compared by their numbers. A cast or a derived
  // `==` would do, but a verification tool that follows every path through
  // a function then follows one for each pair of constructors.
  out << "}\nimpl PartialEq for Constructor {\nfn eq(&self, other: &Self) -> "
         "bool { self.code() == other.code() }\n}\nimpl Eq for Constructor "
         "{}\nimpl Constructor {\n/// The place of the constructor in the "
         "enum.\npub fn code(self) -> u32 { match self {\n";
  size_t code = 0;
  for (const auto& c : d_constructors)
  {
    out << "Self::" << ident(c.first) << " => " << code++ << ",\n";
  }
  out << "}}\npub fn is_user(self) -> bool { match self {\n";
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
      {"$emb_String", "Str"},
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
  out << "_ => return None, }) }\n}\nimpl std::fmt::Debug for Constructor {\n"
         "fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result "
         "{ f.write_str(match self {\n";
  for (const auto& c : d_constructors)
  {
    out << "Self::" << ident(c.first) << " => " << quote(ident(c.first))
        << ",\n";
  }
  out << "}) }\n}\n"
         "/// The names and constants that generated code passes to the\n"
         "/// runtime as numbers: their places in this list.\n"
         "pub(crate) const NATIVE_TEXTS: &[&str] = &[\n";
  for (const std::string& text : d_nativeTexts)
  {
    out << quote(text) << ",\n";
  }
  out << "];\n";
  return out.str();
}

size_t RustMetaReduce::nativeText(const std::string& text)
{
  for (size_t i = 0; i < d_nativeTexts.size(); ++i)
  {
    if (d_nativeTexts[i] == text)
    {
      return i;
    }
  }
  d_nativeTexts.push_back(text);
  return d_nativeTexts.size() - 1;
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

/** Emits temporaries in evaluation order; no nested mutable borrows. */
class RustMetaReduce::Emitter
{
 public:
  /**
   * What the functions written for one program share: where its helper
   * functions go, its Rust name, and the number of helpers so far.
   */
  struct Shared
  {
    std::ostream& helpers;
    std::string name;
    size_t count = 0;
    /**
     * The trace of what the emitters write (see `TraceNode`): the nodes of
     * the calls made from outside, the nodes being written, and the
     * helpers that the text written outside every node was cut into.
     */
    std::vector<std::unique_ptr<TraceNode>> roots;
    std::vector<TraceNode*> open;
    std::vector<std::string> rootHelpers;
    /**
     * A case, from the roots so far, which are then dropped: the patterns
     * of its `nargs` arguments, then what it gives (`body`), or for the
     * next round of a loop the arguments of that round (`again`).
     */
    std::string takeCase(size_t nargs, bool again)
    {
      std::string ret = "\"patterns\": [";
      for (size_t i = 0; i < nargs && i < roots.size(); ++i)
      {
        ret += (i == 0 ? "" : ", ") + roots[i]->json();
      }
      ret += again ? "], \"again\": [" : "], \"body\": ";
      for (size_t i = nargs; i < roots.size(); ++i)
      {
        ret += (i == nargs ? "" : ", ") + roots[i]->json();
      }
      ret += (again ? "]" : "") + std::string(", \"helpers\": ")
             + jsList(rootHelpers);
      drop();
      return ret;
    }
    void drop()
    {
      roots.clear();
      rootHelpers.clear();
    }
  };
  Emitter(RustMetaReduce& meta, std::ostream& out, Shared& shared)
      : m(meta), o(out), d_shared(shared)
  {
  }
  /**
   * An emitter for a part of what `parent` is writing that becomes a
   * function of its own (a branch of a conditional): it knows the
   * parent's variables and goes on with its numbering.
   */
  Emitter(Emitter& parent, std::ostream& out)
      : vars(parent.vars),
        m(parent.m),
        o(out),
        d_shared(parent.d_shared),
        next(parent.next)
  {
  }
  std::map<Expr, std::string> vars;
  /** Starts the body of another function: no variable is known. */
  void clear() { vars.clear(); }
  /** Opens the node of a call of `expr` or `pattern` (see `TraceNode`). */
  void traceOpen()
  {
    auto n = std::make_unique<TraceNode>();
    TraceNode* at = n.get();
    if (d_shared.open.empty())
    {
      d_shared.roots.push_back(std::move(n));
    }
    else
    {
      d_shared.open.back()->sub.push_back(std::move(n));
    }
    d_shared.open.push_back(at);
  }
  /** The node being written. */
  TraceNode& node() { return *d_shared.open.back(); }
  /** The function and the arguments of `call`, `name(s, x, y)`. */
  void traceCall(const std::string& call)
  {
    node().set("fn", js(call.substr(0, call.find('('))));
    std::vector<std::string> as;
    for (size_t i = call.find('(') + 2; i < call.size();)
    {
      size_t j = call.find_first_of(",)", i);
      std::string arg = call.substr(i, j - i);
      arg.erase(0, arg.find_first_not_of(' '));
      if (!arg.empty())
      {
        as.push_back(arg);
      }
      i = j + 1;
    }
    node().set("args", jsList(as));
  }
  /**
   * The variable of the value of `t`, after the statements that compute
   * it. Its node in the trace says what was written for `t`, with the
   * variable (`v`) and the nodes of the parts of `t`.
   */
  std::string expr(const Expr& t)
  {
    traceOpen();
    std::string v = exprOf(t);
    node().set("v", js(v));
    d_shared.open.pop_back();
    return v;
  }
  /**
   * The statements that test that the term of `value` matches `t`, and
   * bind its parameters. Its node in the trace says what was written for
   * `t`, with `value` and the nodes of the parts of `t`.
   */
  void pattern(const Expr& t, const std::string& value)
  {
    traceOpen();
    patternOf(t, value);
    node().set("value", js(value));
    d_shared.open.pop_back();
  }
  /**
   * A call of the runtime or of a generated function that can fail, with
   * the error returned to the caller. Written as a match, not as `call?`:
   * `?` goes through the `Try` and `From` traits, which is more for the
   * verification tools to translate at each of the many calls and leaves
   * a call of `Try::branch` and a match on `ControlFlow` in their output
   * where this is a match on the result.
   */
  static std::string attempt(const std::string& call)
  {
    return "match " + call + " { Ok(v) => v, Err(e) => return Err(e) }";
  }
  /** `let v<n> = rhs;`, where an `rhs` that ends in `?` is such a call. */
  std::string val(const std::string& rhs) { return let(rhs, true); }
  /**
   * The same for a value that is not a term (a number, an optional pair,
   * the fields of a term), which the next statement uses up: a function
   * does not end between the two.
   */
  std::string part(const std::string& rhs) { return let(rhs, false); }
  std::string let(const std::string& rhs, bool whole)
  {
    std::string n = fresh();
    bool fallible = !rhs.empty() && rhs.back() == '?';
    o << "let " << n << " = "
      << (fallible ? attempt(rhs.substr(0, rhs.size() - 1)) : rhs) << ";\n";
    if (whole)
    {
      o << CUT;
    }
    return n;
  }
  /** The name of a new temporary. */
  std::string fresh() { return "v" + std::to_string(next++); }
  /**
   * Marks, in what an emitter writes, the end of a statement after which
   * a function may end and another go on (see `close`). It is not part
   * of the Rust text.
   */
  static constexpr char CUT = '\x1f';
  /** What is written, without the marks. */
  static std::string plain(const std::string& text)
  {
    std::string ret;
    for (char c : text)
    {
      if (c != CUT)
      {
        ret += c;
      }
    }
    return ret;
  }
  /**
   * The parameters of a function whose body is `text`, and the arguments
   * of a call of it: the variables `text` mentions and does not make
   * itself. All are terms: the arguments of the program (a<i>) and the
   * temporaries (v<i>).
   */
  static std::pair<std::string, std::string> parameters(const std::string& text)
  {
    auto wordChar = [](char c) {
      return std::isalnum(static_cast<unsigned char>(c)) || c == '_';
    };
    auto variable = [](const std::string& w) {
      return w.size() >= 2 && (w[0] == 'a' || w[0] == 'v')
             && w.find_first_not_of("0123456789", 1) == std::string::npos;
    };
    // what `text` makes: the variables between a `let` and its `=`
    std::set<std::string> made;
    for (size_t at = text.find("let "); at != std::string::npos;
         at = text.find("let ", at + 1))
    {
      if (at > 0 && wordChar(text[at - 1]))
      {
        continue;
      }
      size_t end = text.find('=', at);
      for (size_t i = at + 4; i < end && i < text.size();)
      {
        size_t j = i;
        while (j < end && wordChar(text[j]))
        {
          ++j;
        }
        if (j > i && variable(text.substr(i, j - i)))
        {
          made.insert(text.substr(i, j - i));
        }
        i = j > i ? j : i + 1;
      }
    }
    std::string params, args;
    std::set<std::string> seen;
    for (size_t i = 0; i < text.size();)
    {
      size_t j = i;
      while (j < text.size() && wordChar(text[j]))
      {
        ++j;
      }
      if (j == i)
      {
        ++i;
        continue;
      }
      std::string word = text.substr(i, j - i);
      i = j;
      if (variable(word) && made.count(word) == 0 && seen.insert(word).second)
      {
        params += ", " + word + ": Term";
        args += ", " + word;
      }
    }
    return {params, args};
  }
  /**
   * The end of a function that returns `ret`: the statements `body` and
   * then the expression `result`. A long body is cut: the function ends
   * with a call of a new function of this program, which goes on with
   * the rest and gets the variables the rest uses. A function with
   * hundreds of fallible calls in a row is more than the tools this code
   * is translated with take (Charon's reconstruction of the control flow
   * nests once per call), and in the Lean that Aeneas writes the rest of
   * a function is nested once more at each such call and each pattern:
   * past about seventeen levels its printer breaks a line where Lean
   * cannot read it.
   */
  std::string close(const std::string& body,
                    const std::string& result,
                    const std::string& ret)
  {
    const size_t limit = 12;
    size_t cut = std::string::npos, seen = 0;
    for (size_t i = 0; i < body.size(); ++i)
    {
      if (body[i] == CUT && ++seen == limit)
      {
        cut = i + 1;
        break;
      }
    }
    if (cut == std::string::npos || cut >= body.size())
    {
      return plain(body) + result + "\n";
    }
    std::string rest = body.substr(cut);
    std::string name = "more_" + std::to_string(d_shared.count++) + "_"
                       + d_shared.name;
    auto pa = parameters(plain(rest) + " " + result);
    (d_shared.open.empty() ? d_shared.rootHelpers : d_shared.open.back()->helpers)
        .push_back(name);
    std::string tail = close(rest, result, ret);
    d_shared.helpers << "fn " << name << "(s: &mut Store" << pa.first << ") -> "
                     << ret << " {\n"
                     << tail << "}\n";
    return plain(body.substr(0, cut)) + name + "(s" + pa.second + ")\n";
  }
  /** What a pattern that does not match does: the case does not apply. */
  const std::string fail = " { return Ok(None); }\n";
  /**
   * A function of this program with the body `body`, which computes a
   * term, and the call of it. `extra` are parameters with their
   * arguments; the others are the variables the body uses.
   */
  std::string helper(const std::string& kind,
                     const std::vector<std::pair<std::string, std::string>>&
                         extra,
                     const std::string& body)
  {
    std::string name = kind + "_" + std::to_string(d_shared.count++) + "_"
                       + d_shared.name;
    std::string params, args;
    for (const auto& x : extra)
    {
      params += ", " + x.first + ": Term";
      args += ", " + x.second;
    }
    auto pa = parameters(body);
    d_shared.helpers << "fn " << name << "(s: &mut Store" << params << pa.first
                     << ") -> CheckResult<Term> {\n"
                     << body << "}\n";
    return name + "(s" + args + pa.second + ")";
  }
  /**
   * The integer whose decimal text is `text`, as a value: `Integer::from`
   * of a `u32`, negated if need be, which the proofs take from the specs of
   * `from` and `neg`. A number that does not fit is built from 32-bit
   * limbs, the most significant first (`x * 2^32 + limb`); no signature
   * has one today.
   */
  std::string integer(const std::string& text)
  {
    bool neg = !text.empty() && text[0] == '-';
    std::string digits = neg ? text.substr(1) : text;
    if (digits.empty()
        || digits.find_first_not_of("0123456789") != std::string::npos)
    {
      EO_FATAL() << "rust-meta: not an integer: " << text;
    }
    // the limbs, by long division of the decimal digits by 2^32
    std::vector<uint32_t> limbs;
    std::string rest = digits;
    while (rest != "0" && !rest.empty())
    {
      std::string q;
      uint64_t r = 0;
      for (char c : rest)
      {
        r = r * 10 + static_cast<uint64_t>(c - '0');
        uint64_t d = r >> 32;
        if (!q.empty() || d != 0)
        {
          q += static_cast<char>('0' + d);
        }
        r &= 0xffffffffULL;
      }
      limbs.push_back(static_cast<uint32_t>(r));
      rest = q.empty() ? "0" : q;
    }
    if (limbs.empty())
    {
      limbs.push_back(0);
    }
    std::string v = "Integer::from(" + std::to_string(limbs.back()) + "u32)";
    for (size_t i = limbs.size() - 1; i > 0; --i)
    {
      v = v + ".mul(&Integer::from(65536u32).mul(&Integer::from(65536u32))).add(&Integer::from("
          + std::to_string(limbs[i - 1]) + "u32))";
    }
    return neg ? v + ".neg()" : v;
  }
  /** The code points of a string written as `"…"` in a signature. */
  static std::string codePoints(const std::string& quoted)
  {
    std::string inner = quoted.substr(1, quoted.size() - 2);
    inner = replace_all(inner, "\"\"", "\"");
    std::ostringstream out;
    out << "EoString::from_code_points(vec![";
    // (the string must outlive the loop: `getVec` is a reference into it)
    const String str(inner, true);
    for (unsigned c : str.getVec())
    {
      out << c << ',';
    }
    out << "])";
    return out.str();
  }
  /** The value of a literal. */
  std::string literal(const Expr& e)
  {
    const Literal* l = e.getValue()->asLiteral();
    switch (e.getKind())
    {
      case Kind::BOOLEAN:
        return l->d_bool ? "Lit::Boolean(true)" : "Lit::Boolean(false)";
      case Kind::NUMERAL: return "Lit::Numeral(" + integer(l->d_int.toString()) + ")";
      case Kind::RATIONAL:
      case Kind::DECIMAL:
      {
        // `n/d` in lowest terms, `d` positive
        std::string text = l->d_rat.toString();
        size_t slash = text.find('/');
        std::string n = text.substr(0, slash);
        std::string d = slash == std::string::npos ? "1" : text.substr(slash + 1);
        return "Lit::Rational("
               + part("match Rational::from_integers(&" + integer(n) + ", &"
                      + integer(d)
                      + ") { Some(q) => q, None => return "
                        "Err(CheckError::InvalidNative) }")
               + ")";
      }
      case Kind::BINARY:
      case Kind::HEXADECIMAL:
        return "Lit::Binary(BitVec::new("
               + std::to_string(l->d_bv.getSize()) + ", &"
               + integer(l->d_bv.getValue().toString()) + "))";
      case Kind::STRING:
      {
        std::ostringstream out;
        out << "Lit::Str(EoString::from_code_points(vec![";
        for (unsigned c : l->d_str.getVec())
        {
          out << c << ',';
        }
        out << "]))";
        return out.str();
      }
      default: EO_FATAL() << "rust-meta: unsupported literal " << e;
    }
    return "";
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
      if (name == "z_max_code_point")
      {
        return "s.native_max_code_point()?";
      }
      // a numeral or a string, as a value
      if (!name.empty() && name.find_first_not_of("-0123456789") == std::string::npos
          && name.find_first_of("0123456789") != std::string::npos)
      {
        return "s.raw(Lit::Numeral(" + integer(name) + "))?";
      }
      if (name.size() >= 2 && name.front() == '"' && name.back() == '"')
      {
        return "s.raw(Lit::Str(" + codePoints(name) + "))?";
      }
      // anything else the runtime reads (and refuses)
      return "s.native_constant(" + std::to_string(m.nativeText(name)) + ")?";
    }
    auto it = ops.find(name);
    if (it == ops.end() || it->second.second != nargs)
    {
      return "s.unsupported_native(" + std::to_string(m.nativeText(name))
             + ")?";
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
    return "s.native_pattern_constant(" + std::to_string(m.nativeText(name))
           + ", " + value + ")?";
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
  /**
   * A conditional is a function of its own, called here: its branches
   * compute, and can fail, and written in place they would be arms of a
   * match that the rest of the case follows.
   */
  std::string conditional(const Expr& c,
                          const Expr& yes,
                          const Expr& no,
                          bool native)
  {
    std::string cv = expr(c);
    node().set("ite", native ? "\"native\"" : "\"eo\"");
    node().set("next_var", std::to_string(next));
    std::ostringstream ys, ns;
    Emitter ye(*this, ys);
    std::string a = ye.expr(yes);
    next = ye.next;
    Emitter ne(*this, ns);
    std::string b = ne.expr(no);
    next = ne.next;
    const std::string ret = "CheckResult<Term>";
    std::string body =
        "let branch = "
        + attempt(std::string("s.boolean_value(condition, ")
                  + (native ? "true" : "false") + ")")
        + ";\nmatch branch {\nSome(true) => {\n"
        + close(ys.str(), "Ok(" + a + ")", ret) + "}\nSome(false) => {\n"
        + close(ns.str(), "Ok(" + b + ")", ret)
        + "}\nNone => Ok(s.stuck()),\n}\n";
    std::string call = helper("if", {{"condition", cv}}, body);
    traceCall(call);
    return val(call + "?");
  }
  std::string op(Kind k, const Expr& t, size_t start)
  {
    node().set("eval", js(evalOp(k)));
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
      // A function of its own, as a conditional is.
      std::string a = expr(t[start]), b = expr(t[start + 1]);
      std::ostringstream rs;
      Emitter re(*this, rs);
      std::string r = re.expr(t[start + 2]);
      next = re.next;
      std::string body = "if " + a + " != " + b
                         + " { return Ok(s.stuck()); }\nlet stuck = "
                         + attempt("s.is_stuck(" + a + ")")
                         + ";\nif stuck { return Ok(s.stuck()); }\n"
                         + close(rs.str(), "Ok(" + r + ")", "CheckResult<Term>");
      std::string call = helper("requires", {}, body);
      traceCall(call);
      return val(call + "?");
    }
    std::string as = args(t, start);
    if (k == Kind::EVAL_TYPE_OF || k == Kind::EVAL_NIL
        || k == Kind::EVAL_DT_CONSTRUCTORS || k == Kind::EVAL_DT_SELECTORS)
    {
      return val(ident("$eo_" + kindToTerm(k).substr(4)) + "(s, " + as + ")?");
    }
    // Name the runtime's operator, so the C++ and Rust enum declaration
    // orders are independent. The runtime validates arities itself.
    // The list operators are above the functions they call; the others
    // are in the runtime that all generated code rests on.
    bool list = k == Kind::EVAL_CONS || starts(evalOp(k), "List");
    return val(std::string(list ? "s.builtin_list" : "s.builtin_core")
               + "(EvalOp::" + evalOp(k) + ", &[" + as + "])?");
  }
  std::string exprOf(const Expr& t)
  {
    auto var = vars.find(t);
    if (var != vars.end())
    {
      node().set("op", "\"param\"");
      return var->second;
    }
    Kind k = t.getKind();
    if (isLiteral(k))
    {
      std::ostringstream kind;
      kind << k;
      node().set("op", "\"literal\"");
      node().set("kind", js(kind.str()));
      if (k == Kind::BOOLEAN)
      {
        node().set("bool", t.getValue()->asLiteral()->d_bool ? "true" : "false");
      }
      return val("s.literal(" + literal(t) + ")?");
    }
    if (k == Kind::EVAL_MAX_CODE_POINT)
    {
      // the numeral that is the maximum code point of the checker
      return val("s.literal(Lit::Numeral(Integer::from(MAX_CODE_POINT)))?");
    }
    if (t.getNumChildren() == 0)
    {
      if (k == Kind::PARAM)
      {
        EO_FATAL() << "rust-meta: unbound parameter " << t;
      }
      if (k == Kind::PROGRAM_CONST)
      {
        node().set("op", "\"program_const\"");
        node().set("program", js(getName(t)));
        return val(ident(getName(t)) + "(s)?");
      }
      std::string n = k == Kind::TYPE        ? "$emb_Type"
                      : k == Kind::BOOL_TYPE ? "$emb_Bool"
                                             : getName(t);
      node().set("op", "\"constant\"");
      node().set("ctor", js(n));
      return val("s.construct(" + ctor(n) + ", &[])?");
    }
    if (k == Kind::APPLY_OPAQUE)
    {
      std::string n = getName(t[0]);
      if (starts(n, "$native_apply_"))
      {
        std::string name = getName(t[1]);
        node().set("op", "\"native\"");
        node().set("name", js(name));
        node().set("nargs", std::to_string(t.getNumChildren() - 2));
        if (name == "ite" && t.getNumChildren() == 5)
        {
          return conditional(t[2], t[3], t[4], true);
        }
        std::string as = args(t, 2);
        return val(native(name, t.getNumChildren() - 2, as));
      }
      node().set("op", "\"construct\"");
      node().set("ctor", js(n));
      std::string as = args(t, 1);
      return val("s.construct(" + ctor(n) + ", &[" + as + "])?");
    }
    if (k == Kind::APPLY && t[0].getKind() == Kind::PROGRAM_CONST)
    {
      std::string n = getName(t[0]);
      Kind b = builtin(n);
      if (b != Kind::NONE)
      {
        node().set("op", "\"builtin\"");
        node().set("program", js(n));
        return op(b, t, 1);
      }
      node().set("op", "\"call\"");
      node().set("program", js(n));
      std::string as = args(t, 1);
      return val(ident(n) + "(s" + (as.empty() ? "" : ", " + as) + ")?");
    }
    if (isLiteralOp(k))
    {
      node().set("op", "\"builtin\"");
      return op(k, t, 0);
    }
    if (k == Kind::FUNCTION_TYPE)
    {
      size_t n = t.getNumChildren();
      // the result type first, then each argument type from the last, each
      // applied to the arrows to its right: `rounds` names, for each, the
      // constant, its application to the argument, and the whole
      node().set("op", "\"funtype\"");
      node().set("guarded", n == 2 && t.isEvaluatable() ? "true" : "false");
      std::string tail = expr(t[n - 1]);
      std::string rounds = "[";
      for (size_t i = n - 1; i > 0; --i)
      {
        std::string a = expr(t[i - 1]);
        std::string h = val(named("$emb_FunType", ""));
        std::string f = val("s.apply(" + h + ", " + a + ")?");
        tail = val("s.apply(" + f + ", " + tail + ")?");
        rounds += std::string(i == n - 1 ? "" : ", ") + "{\"fun\": " + js(h)
                  + ", \"applied\": " + js(f) + ", \"v\": " + js(tail) + "}";
      }
      node().set("rounds", rounds + "]");
      return tail;
    }
    if (k == Kind::APPLY && t.getNumChildren() == 2)
    {
      // `guarded`: lean-meta writes the application with `__eo_mk_apply`
      node().set("op", "\"apply\"");
      node().set("guarded", t.isEvaluatable() ? "true" : "false");
      std::string f = expr(t[0]), a = expr(t[1]);
      return val("s.apply(" + f + ", " + a + ")?");
    }
    if (k == Kind::VARIABLE)
    {
      node().set("op", "\"variable\"");
      std::string as = args(t, 0);
      return val(named("$emb_Var", as));
    }
    EO_FATAL() << "rust-meta: unsupported expression " << t << " (" << k << ")";
    return "";
  }
  void patternOf(const Expr& t, const std::string& value)
  {
    Kind k = t.getKind();
    if (k == Kind::PARAM)
    {
      auto it = vars.find(t);
      if (it != vars.end())
      {
        // a parameter the pattern has already bound: an equality test
        node().set("pat", "\"same\"");
        node().set("other", js(it->second));
        o << "if " << value << " != " << it->second << fail << CUT;
      }
      else
      {
        node().set("pat", "\"param\"");
        vars[t] = value;
      }
      return;
    }
    if (k == Kind::FUNCTION_TYPE && t.getNumChildren() == 2)
    {
      std::string outer = part("s.unapply(" + value + ")?");
      std::string f = fresh(), r = fresh();
      o << "let Some((" << f << ", " << r << ")) = " << outer << " else" << fail
        << ";\n"
        << CUT;
      std::string inner = part("s.unapply(" + f + ")?");
      std::string op = fresh(), l = fresh();
      o << "let Some((" << op << ", " << l << ")) = " << inner << " else"
        << fail << ";\n"
        << CUT;
      std::string fun = part("s.is_node(" + op + ", "
                            + m.constructorOption("$emb_FunType") + ")?");
      o << "if !" << fun << fail << CUT;
      // `value` is `(f r)`, `f` is `(op l)`, `op` the node of $emb_FunType
      node().set("pat", "\"funtype\"");
      node().set("f", js(f));
      node().set("r", js(r));
      node().set("op", js(op));
      node().set("l", js(l));
      pattern(t[0], l);
      pattern(t[1], r);
      return;
    }
    if (k == Kind::APPLY && t.getNumChildren() == 2)
    {
      std::string parts = part("s.unapply(" + value + ")?");
      std::string f = fresh(), a = fresh();
      o << "let Some((" << f << ", " << a << ")) = " << parts << " else" << fail
        << ";\n"
        << CUT;
      node().set("pat", "\"apply\"");
      node().set("f", js(f));
      node().set("a", js(a));
      pattern(t[0], f);
      pattern(t[1], a);
      return;
    }
    if (k == Kind::APPLY_OPAQUE || k == Kind::VARIABLE)
    {
      size_t start = k == Kind::VARIABLE ? 0 : 1;
      std::string n = k == Kind::VARIABLE ? "$emb_Var" : getName(t[0]);
      std::string found;
      if (starts(n, "$native_apply_"))
      {
        node().set("pat", "\"native\"");
        node().set("name", js(getName(t[1])));
        found = part(nativePattern(getName(t[1]), value));
        start = 2;
      }
      else
      {
        node().set("pat", "\"ctor\"");
        node().set("ctor", js(n));
        found = part("s.destruct(" + ctor(n) + ", " + value + ")?");
      }
      // The fields are taken out at once, each into a variable, so that
      // every variable of the generated code is a term.
      o << "let Some(fields) = " << found << " else" << fail << ";\n";
      std::vector<std::string> fields;
      for (size_t i = start; i < t.getNumChildren(); ++i)
      {
        fields.push_back(fresh());
        o << "let " << fields.back() << " = fields[" << (i - start) << "];\n";
      }
      o << CUT;
      node().set("fields", jsList(fields));
      for (size_t i = start; i < t.getNumChildren(); ++i)
      {
        pattern(t[i], fields[i - start]);
      }
      return;
    }
    if (isLiteral(k) || t.getNumChildren() == 0)
    {
      // a value: an equality test with the term built
      node().set("pat", "\"value\"");
      std::string expected = expr(t);
      o << "if " << value << " != " << expected << fail << CUT;
      return;
    }
    EO_FATAL() << "rust-meta: unsupported pattern " << t;
  }

 private:
  RustMetaReduce& m;
  std::ostream& o;
  Shared& d_shared;
  size_t next = 0;
};

std::string RustMetaReduce::emitProgram(const std::string& name,
                                        const Program& p)
{
  // A program is a public function that keeps the budgets and the cache,
  // and calls `body_<name>` for the result. A program with cases has one
  // function per case, which returns `None` where its patterns do not
  // match, and the body tries them in order. Nothing here is a closure, a
  // labelled block or a labelled loop, and no function is long because
  // the program has many cases: the verification tools this code is
  // translated with follow every path through a function.
  std::ostringstream out, helpers;
  const std::string id = ident(name);
  Emitter::Shared shared{helpers, id};
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
  std::string params, args;
  for (size_t i = 0; i < nargs; ++i)
  {
    params += ", a" + std::to_string(i) + ": Term";
    args += ", a" + std::to_string(i);
  }
  auto attempt = [](const std::string& call) { return Emitter::attempt(call); };
  // The program's entry in the trace (see `d_trace`).
  std::ostringstream tr;
  tr << "\"name\": " << js(name) << ", \"id\": " << js(id);
  auto typeOf = [&](const Expr& t) {
    std::ostringstream text;
    text << t;
    return "{\"type\": " + js(text.str()) + ", \"meta\": "
           + js(metaKindToString(getTypeMetaKindFor(t, MetaKind::EUNOIA, true)))
           + "}";
  };
  if (cases)
  {
    tr << ", \"args\": [";
    for (size_t i = 0; i < nargs; ++i)
    {
      tr << (i == 0 ? "" : ", ") << typeOf(ty[i]);
    }
    tr << "], \"ret\": " << typeOf(ty[nargs]);
  }
  switch (d_cacheKinds.at(name))
  {
    case CacheKind::NONE: tr << ", \"cache\": {\"kind\": \"none\"}"; break;
    case CacheKind::PROGRAM:
      tr << ", \"cache\": {\"kind\": \"program\", \"id\": "
         << d_programIds.at(name) << "}";
      break;
    case CacheKind::EO_TYPE: tr << ", \"cache\": {\"kind\": \"eo_type\"}"; break;
    default: tr << ", \"cache\": {\"kind\": \"smt_type\"}"; break;
  }
  auto record = [&](const std::string& rest) {
    d_trace.emplace_back(name, tr.str() + rest);
  };
  // The checking loop's premise lookup walks the state list one element at
  // a time, creating and interning a native numeral at each one. Where the
  // loop's constructors are the expected ones, it is compiled to the
  // runtime's Store::state_nth, which finds the same element with a
  // machine counter (see its documentation in runtime/lib.rs.in).
  if (name == "$eo_state_proven_nth" && cases && nargs == 2
      && d_cacheKinds.at(name) == CacheKind::NONE
      && d_constructors.count("$emb_s.cons") > 0
      && d_programs.count("$eo_StateObj_proven") > 0)
  {
    out << "// EO program " << quote(name)
        << ", compiled to Store::state_nth\npub fn " << id
        << "(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {\n"
        << attempt("s.enter()")
        << ";\nlet result = match s.state_nth(Constructor::"
        << ident("$emb_s.cons") << ", a0, a1) {\nOk(Some(element)) => "
        << ident("$eo_StateObj_proven")
        << "(s, element),\nOk(None) => s.boolean(true),\nErr(e) => Err(e),\n"
        << "};\ns.leave();\nresult\n}\n";
    record(", \"kind\": \"state_nth\", \"calls\": "
           + jsList({"$eo_StateObj_proven"}));
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
      // `scan` goes down the list of arguments, a step at a time, keeping
      // each guard with its term; `unwind` then pushes them from the last
      // to the first.
      out << "// EO program " << quote(name)
          << ", compiled to an iterative guarded fold\npub fn " << id
          << "(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {\n"
          << attempt("s.enter()") << ";\nlet result = body_" << id
          << "(s, a0, a1);\ns.leave();\nresult\n}\n"
          << "fn body_" << id
          << "(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {\n"
          << "let scanned = " << attempt("scan_" + id + "(s, a0, a1)")
          << ";\nunwind_" << id << "(s, scanned.0, &scanned.1)\n}\n"
          << "fn scan_" << id
          << "(s: &mut Store, a0: Term, a1: Term) -> CheckResult<(Term, "
             "Vec<(Term, Term)>)> {\nlet mut pending = Vec::new();\n"
             "let mut args = a1;\nloop {\nmatch step_"
          << id
          << "(s, a0, args) {\nOk(FoldStep::Done(state)) => return Ok((state, "
             "pending)),\nOk(FoldStep::Push(guard, term, tail)) => {\n"
             "pending.push((guard, term));\nargs = tail;\n}\n"
             "Err(e) => return Err(e),\n}\n}\n}\n"
          << "fn step_" << id
          << "(s: &mut Store, a0: Term, a1: Term) -> CheckResult<FoldStep> "
             "{\nif let Some(step) = "
          << attempt("case_0_" + id + "(s, a0, a1)")
          << " { return Ok(step); }\nif let Some(step) = "
          << attempt("case_1_" + id + "(s, a0, a1)")
          << " { return Ok(step); }\nOk(FoldStep::Done(s.stuck()))\n}\n"
          << "fn case_0_" << id
          << "(s: &mut Store, a0: Term, a1: Term) -> "
             "CheckResult<Option<FoldStep>> {\n";
      const std::string ret = "CheckResult<Option<FoldStep>>";
      std::ostringstream c0, c1;
      Emitter e0(*this, c0, shared);
      e0.pattern(base[1], "a0");
      e0.pattern(base[2], "a1");
      out << e0.close(c0.str(), "Ok(Some(FoldStep::Done(a0)))", ret)
          << "}\nfn case_1_" << id
          << "(s: &mut Store, a0: Term, a1: Term) -> "
             "CheckResult<Option<FoldStep>> {\n";
      Emitter e(*this, c1, shared);
      e.pattern(step[1], "a0");
      e.pattern(step[2], "a1");
      std::string guard = e.expr(body[1]), term = e.expr(body[2]);
      std::string tail = e.expr(body[3][2]);
      // One tick replaces each recursive enter, keeping the call budget
      // while making the depth independent of the number of assumptions.
      c1 << attempt("s.tick()") << ";\n" << Emitter::CUT;
      out << e.close(c1.str(),
                     "Ok(Some(FoldStep::Push(" + guard + ", " + term + ", "
                         + tail + ")))",
                     ret)
          << "}\n"
          << "fn unwind_" << id
          << "(s: &mut Store, state: Term, pending: &[(Term, Term)]) -> "
             "CheckResult<Term> {\nlet mut state = state;\n"
             "let mut i = pending.len();\nwhile i > 0 {\ni -= 1;\n"
             "let (guard, term) = pending[i];\nstate = "
          << attempt(ident(getName(body[0])) + "(s, guard, term, state)")
          << ";\n}\nOk(state)\n}\n"
          << helpers.str();
      shared.drop();
      // the guard, where it is the conjunction of two programs applied to
      // the element (`guard_calls`), and the push
      const Expr elem = step[2][1];
      auto callee = [&](const Expr& x) {
        return x.getKind() == Kind::APPLY && x.getNumChildren() == 2
                       && x[0].getKind() == Kind::PROGRAM_CONST && x[1] == elem
                   ? getName(x[0])
                   : std::string();
      };
      Expr g = body[1];
      size_t g0 = 0;
      bool isAnd = g.getKind() == Kind::EVAL_AND && g.getNumChildren() == 2;
      if (!isAnd && g.getKind() == Kind::APPLY && g.getNumChildren() == 3
          && g[0].getKind() == Kind::PROGRAM_CONST
          && builtin(getName(g[0])) == Kind::EVAL_AND)
      {
        isAnd = true;
        g0 = 1;
      }
      std::string guardCalls = "null";
      if (isAnd && !callee(g[g0]).empty() && !callee(g[g0 + 1]).empty())
      {
        guardCalls = jsList({callee(g[g0]), callee(g[g0 + 1])});
      }
      record(", \"kind\": \"assume_fold\", \"guard_calls\": " + guardCalls
             + ", \"push\": " + js(getName(body[0])));
      return out.str();
    }
  }
  out << "// EO program " << quote(name) << "\npub fn " << id << "(s: &mut Store"
      << params << ") -> CheckResult<Term> {\n"
      << attempt("s.enter()") << ";\n";
  CacheKind cache = d_cacheKinds.at(name);
  std::string cachePut;
  if (cache != CacheKind::NONE)
  {
    out << "let cache_args = [";
    for (size_t i = 0; i < nargs; ++i)
    {
      out << (i == 0 ? "" : ", ") << "a" << i;
    }
    out << "];\n";
    std::string get;
    if (cache == CacheKind::PROGRAM)
    {
      std::string pid =
          "ProgramId(" + std::to_string(d_programIds.at(name)) + ")";
      get = "s.cached_program(" + pid + ", &cache_args)";
      cachePut = attempt("s.cache_program(" + pid + ", &cache_args, value)") + ";";
    }
    else
    {
      std::string kind = cache == CacheKind::EO_TYPE ? "TypeCacheKind::Eunoia"
                                                     : "TypeCacheKind::Smt";
      get = "s.cached_type(" + kind + ", cache_args[0])";
      cachePut = attempt("s.cache_type(" + kind + ", cache_args[0], value)") + ";";
    }
    out << "match " << get << " {\n"
        << "Ok(Some(value)) => { s.leave(); return Ok(value); },\n"
        << "Ok(None) => {},\n"
        << "Err(error) => { s.leave(); return Err(error); },\n}\n";
  }
  out << "let result = body_" << id << "(s" << args << ");\ns.leave();\n";
  if (!cachePut.empty())
  {
    out << "if let Ok(value) = result { " << cachePut << " }\n";
  }
  out << "result\n}\n";
  if (!cases)
  {
    out << "fn body_" << id << "(s: &mut Store) -> CheckResult<Term> {\n";
    std::ostringstream body;
    Emitter e(*this, body, shared);
    std::string v = e.expr(p.body);
    out << e.close(body.str(), "Ok(" + v + ")", "CheckResult<Term>") << "}\n"
        << helpers.str();
    shared.drop();
    record(", \"kind\": \"define\"");
    return out.str();
  }
  // What a case gives: a term, or, for a program whose tail calls are a
  // loop, a term or the arguments of the next round.
  const std::string result =
      loop ? "Next<[Term; " + std::to_string(nargs) + "]>" : "Term";
  const std::string stuck = loop ? "Next::Done(s.stuck())" : "s.stuck()";
  const size_t ncases = p.body.getNumChildren();
  // Where the body tries the cases: in order, the first that applies.
  std::ostringstream tries;
  std::vector<std::string> stuckArgs;
  if (!p.isDefine)
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
      for (size_t i = 0; i < nargs; ++i)
      {
        if (kinds[i] == MetaKind::EUNOIA)
        {
          stuckArgs.push_back(std::to_string(i));
          tries << "let stuck" << i << " = "
                << attempt("s.is_stuck(a" + std::to_string(i) + ")")
                << ";\nif stuck" << i << " { return Ok(" << stuck << "); }\n";
        }
      }
    }
  }
  auto attemptCase = [&](std::ostream& to, const std::string& fn, bool group) {
    to << "if let Some(found) = " << attempt(fn + "(s" + args + ")")
       << (group ? " { return Ok(Some(found)); }\n" : " { return Ok(found); }\n");
  };
  // A program with many cases tries them in groups of four, the groups in
  // groups of four, and so on, so that no function tries more than four
  // things in a row (each try nests the rest of its function twice in the
  // Lean, see `close`).
  const size_t groupSize = 4;
  std::vector<std::string> level;
  // for the trace: what each entry of `level` tries, as JSON (its name and
  // the cases [lo, hi) it tries), and the groups written
  std::vector<std::string> members;
  std::vector<std::pair<size_t, size_t>> ranges;
  std::string groups;
  auto member = [&](const std::string& fn, size_t lo, size_t hi) {
    return "{\"name\": " + js(fn) + ", \"lo\": " + std::to_string(lo)
           + ", \"hi\": " + std::to_string(hi) + "}";
  };
  for (size_t c = 0; c < ncases; ++c)
  {
    level.push_back("case_" + std::to_string(c) + "_" + id);
    members.push_back(member(level.back(), c, c + 1));
    ranges.emplace_back(c, c + 1);
  }
  for (size_t depth = 0; level.size() > groupSize; ++depth)
  {
    std::vector<std::string> above, aboveMembers;
    std::vector<std::pair<size_t, size_t>> aboveRanges;
    for (size_t g = 0; g * groupSize < level.size(); ++g)
    {
      std::string group = "cases_" + std::to_string(depth) + "_"
                          + std::to_string(g) + "_" + id;
      above.push_back(group);
      size_t first = g * groupSize,
             last = std::min(level.size(), (g + 1) * groupSize) - 1;
      std::string tried;
      for (size_t c = first; c <= last; ++c)
      {
        tried += (c == first ? "" : ", ") + members[c];
      }
      groups += std::string(groups.empty() ? "" : ", ") + "{\"name\": "
                + js(group) + ", \"lo\": " + std::to_string(ranges[first].first)
                + ", \"hi\": " + std::to_string(ranges[last].second)
                + ", \"members\": [" + tried + "]}";
      aboveMembers.push_back(
          member(group, ranges[first].first, ranges[last].second));
      aboveRanges.emplace_back(ranges[first].first, ranges[last].second);
      helpers << "fn " << group << "(s: &mut Store" << params
              << ") -> CheckResult<Option<" << result << ">> {\n";
      for (size_t c = g * groupSize;
           c < level.size() && c < (g + 1) * groupSize;
           ++c)
      {
        attemptCase(helpers, level[c], true);
      }
      helpers << "Ok(None)\n}\n";
    }
    level = above;
    members = aboveMembers;
    ranges = aboveRanges;
  }
  for (const std::string& fn : level)
  {
    attemptCase(tries, fn, false);
  }
  if (loop)
  {
    // A tail call is the next round of a loop: a round is `step_<name>`,
    // which gives the result or the arguments of the next round.
    out << "fn body_" << id << "(s: &mut Store";
    for (size_t i = 0; i < nargs; ++i)
    {
      out << ", mut a" << i << ": Term";
    }
    out << ") -> CheckResult<Term> {\nloop {\nmatch step_" << id << "(s" << args
        << ") {\nOk(Next::Done(value)) => return Ok(value),\n"
        << "Ok(Next::Again(next)) => {\n";
    for (size_t i = 0; i < nargs; ++i)
    {
      out << "a" << i << " = next[" << i << "];\n";
    }
    out << "}\nErr(e) => return Err(e),\n}\n}\n}\nfn step_" << id
        << "(s: &mut Store" << params << ") -> CheckResult<" << result
        << "> {\n"
        << attempt("s.tick()") << ";\n";
  }
  else
  {
    out << "fn body_" << id << "(s: &mut Store" << params
        << ") -> CheckResult<Term> {\n";
  }
  out << tries.str() << "Ok(" << stuck << ")\n}\n";
  std::string traced;
  for (size_t c = 0; c < ncases; ++c)
  {
    Expr pat = p.body[c][0];
    if (pat.getNumChildren() != nargs + 1)
    {
      EO_FATAL() << "rust-meta: bad pattern arity for " << name;
    }
    Expr body = p.body[c][1];
    const std::string ret = "CheckResult<Option<" + result + ">>";
    out << "fn case_" << c << "_" << id << "(s: &mut Store" << params << ") -> "
        << ret << " {\n";
    std::ostringstream cs;
    Emitter e(*this, cs, shared);
    for (size_t j = 0; j < nargs; ++j)
    {
      e.pattern(pat[j + 1], "a" + std::to_string(j));
    }
    std::string value;
    const bool again = loop && tailCall(body);
    if (again)
    {
      // Every argument is evaluated before the next round has any.
      value = "Next::Again([";
      for (size_t j = 1; j <= nargs; ++j)
      {
        value += (j == 1 ? "" : ", ") + e.expr(body[j]);
      }
      value += "])";
    }
    else
    {
      std::string v = e.expr(body);
      value = loop ? "Next::Done(" + v + ")" : v;
    }
    out << e.close(cs.str(), "Ok(Some(" + value + "))", ret) << "}\n";
    traced += std::string(c == 0 ? "" : ",\n      ") + "{"
              + shared.takeCase(nargs, again) + "}";
  }
  std::string top, stuckList;
  for (size_t i = 0; i < members.size(); ++i)
  {
    top += (i == 0 ? "" : ", ") + members[i];
  }
  for (size_t i = 0; i < stuckArgs.size(); ++i)
  {
    stuckList += (i == 0 ? "" : ", ") + stuckArgs[i];
  }
  record(std::string(", \"kind\": \"cases\", \"loop\": ")
         + (loop ? "true" : "false") + ", \"stuck\": [" + stuckList
         + "], \"groups\": [" + groups + "], \"top\": [" + top
         + "],\n    \"cases\": [\n      " + traced + "]");
  // Helpers are module items; emit them after the functions that call them.
  out << helpers.str();
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
  // Every function written for the programs, in the order written, to be
  // put into modules below.
  struct Function
  {
    std::string name;
    std::string text;
    size_t lines = 0;
    std::vector<size_t> calls;
  };
  std::vector<Function> functions;
  std::map<std::string, size_t> functionIndex;
  auto collect = [&](const std::string& text) {
    // A function begins at its `fn` line, or at the comment before it.
    std::istringstream in(text);
    std::string line;
    bool commented = false;
    while (std::getline(in, line))
    {
      bool comment = starts(line, "// EO program ");
      bool head = starts(line, "pub fn ") || starts(line, "fn ");
      if (!comment && (starts(line, "//") || starts(line, "#[")))
      {
        // It would be taken for the end of the function before it, which
        // may go to another module than the function it belongs to.
        EO_FATAL() << "rust-meta: a comment or an attribute that the "
                      "division into functions does not know: "
                   << line;
      }
      if (comment || (head && !commented))
      {
        functions.emplace_back();
      }
      commented = comment;
      if (head)
      {
        size_t at = line.find("fn ") + 3;
        functions.back().name = line.substr(at, line.find('(') - at);
        functionIndex[functions.back().name] = functions.size() - 1;
        // every function can be called from another module of the crate's
        // `generated`, and from nowhere else unless it is a program
        if (starts(line, "fn "))
        {
          line = "pub(super) " + line;
        }
      }
      functions.back().text += line + "\n";
      functions.back().lines++;
    }
  };
  std::ostringstream code, manifest;
  std::vector<std::pair<std::string, std::string>> manifestRows;
  manifest << "source\trust\tlean_identifier\tmodule\n";
  // Complete generation before opening outputs, so unsupported constructs
  // cannot leave behind a partially generated checker.
  for (const auto& n : names)
  {
    collect(emitProgram(n, d_programs.at(n)));
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
    manifestRows.emplace_back(n, lean);
  }
  std::string lib =
      read(getResourcePath("plugins/rust_meta/runtime/lib.rs.in"));
  // The two parts of the runtime that call generated functions: the list
  // operators, and the entry points of checking with the translation
  // checks. They are written among the generated functions (below).
  std::string lists =
      read(getResourcePath("plugins/rust_meta/runtime/lists.rs.in"));
  auto named = [&](std::string text) {
    for (const char* n : {"$eo_typeof",
                          "$eo_nil",
                          "$eo_is_list_nil",
                          "$eo_checker_is_refutation"})
    {
      text = replace_all(text, "@" + std::string(n) + "@", ident(n));
    }
    return text;
  };
  lists = named(lists);
  // (the runtime's own tests call generated functions)
  lib = named(lib);
  // the maximum code point, which this checker is generated for
  lib = replace_all(
      lib, "@MAX_CODE_POINT@", "0x" + [] {
        std::ostringstream ss;
        ss << std::uppercase << std::hex << String::maxCodePoint();
        return ss.str();
      }());
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
      "let _ = t; Err(CheckError::UnsupportedNative("
      + std::to_string(nativeText("SMT translation is unavailable")) + "))";
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
                + "(self, t)? }; self.is_native_true(b)"
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
  checks = named(checks);
  for (const auto& block :
       std::vector<std::pair<std::string, std::string>>{
           {"builtin_list", lists}, {"check_proof_inner", checks}})
  {
    // one function of the call graph each: the block is not divided
    functions.emplace_back();
    functions.back().name = block.first;
    functions.back().text = expandConstructors(block.second);
    functions.back().lines =
        std::count(block.second.begin(), block.second.end(), '\n');
    functionIndex[block.first] = functions.size() - 1;
  }
  // The modules. The functions are grouped so that proofs about them can
  // be made module by module: the tools that translate this code take time
  // and memory in proportion to what they are given (so they are run on
  // one module at a time, the others opaque), and what they produce is
  // imported module by module, which must not go in a circle. So:
  // functions that call each other, directly or through others, are in
  // one module (a strongly connected component of the call graph is never
  // split); a module calls only itself, earlier modules and the runtime;
  // and a module is closed when the next component would take it past a
  // number of lines. The order is that of Tarjan's algorithm over the
  // functions as written, which gives a component after all it calls.
  auto wordChar = [](char c) {
    return std::isalnum(static_cast<unsigned char>(c)) || c == '_';
  };
  for (Function& f : functions)
  {
    std::set<size_t> calls;
    const std::string& text = f.text;
    for (size_t i = 0; i < text.size();)
    {
      size_t j = i;
      while (j < text.size() && wordChar(text[j]))
      {
        ++j;
      }
      if (j == i)
      {
        ++i;
        continue;
      }
      // a call of a generated function: its name, then `(s` (the store
      // is the first argument); a use of a list operator: a call of the
      // method `builtin_list`
      std::string word = text.substr(i, j - i);
      bool defined = i >= 3 && text.compare(i - 3, 3, "fn ") == 0;
      if (!defined
          && (text.compare(j, 2, "(s") == 0
              || (word == "builtin_list" && text.compare(j, 1, "(") == 0)))
      {
        auto it = functionIndex.find(word);
        if (it != functionIndex.end())
        {
          calls.insert(it->second);
        }
      }
      i = j;
    }
    f.calls.assign(calls.begin(), calls.end());
  }
  const size_t none = static_cast<size_t>(-1);
  std::vector<size_t> index(functions.size(), none), low(functions.size(), 0);
  std::vector<bool> onStack(functions.size(), false);
  std::vector<size_t> stack;
  std::vector<std::vector<size_t>> components;
  size_t counter = 0;
  for (size_t root = 0; root < functions.size(); ++root)
  {
    if (index[root] != none)
    {
      continue;
    }
    // (function, the next of its calls to look at)
    std::vector<std::pair<size_t, size_t>> work{{root, 0}};
    index[root] = low[root] = counter++;
    stack.push_back(root);
    onStack[root] = true;
    while (!work.empty())
    {
      size_t v = work.back().first;
      bool descended = false;
      while (work.back().second < functions[v].calls.size())
      {
        size_t w = functions[v].calls[work.back().second++];
        if (index[w] == none)
        {
          index[w] = low[w] = counter++;
          stack.push_back(w);
          onStack[w] = true;
          work.emplace_back(w, 0);
          descended = true;
          break;
        }
        if (onStack[w])
        {
          low[v] = std::min(low[v], index[w]);
        }
      }
      if (descended)
      {
        continue;
      }
      work.pop_back();
      if (!work.empty())
      {
        low[work.back().first] = std::min(low[work.back().first], low[v]);
      }
      if (low[v] == index[v])
      {
        components.emplace_back();
        size_t w;
        do
        {
          w = stack.back();
          stack.pop_back();
          onStack[w] = false;
          components.back().push_back(w);
        } while (w != v);
        // as written
        std::sort(components.back().begin(), components.back().end());
      }
    }
  }
  const size_t partLines = 10000;
  std::vector<std::ostringstream> parts(1);
  std::vector<size_t> partOf(functions.size(), 0);
  size_t lines = 0;
  for (const std::vector<size_t>& component : components)
  {
    size_t size = 0;
    for (size_t f : component)
    {
      size += functions[f].lines;
    }
    if (lines != 0 && lines + size > partLines)
    {
      parts.emplace_back();
      lines = 0;
    }
    lines += size;
    for (size_t f : component)
    {
      partOf[f] = parts.size() - 1;
      parts.back() << functions[f].text;
    }
  }
  for (const Function& f : functions)
  {
    for (size_t callee : f.calls)
    {
      if (partOf[callee] > partOf[functionIndex.at(f.name)])
      {
        EO_FATAL() << "rust-meta: " << f.name << " calls a later module";
      }
    }
  }
  const size_t numParts = parts.size();
  code << "//! The generated functions, in " << numParts
       << " modules. A module's functions call only that module, earlier\n"
          "//! modules and the runtime, and functions that call each other are\n"
          "//! in one module.\n";
  for (size_t k = 0; k < numParts; ++k)
  {
    code << "#[path = \"generated_part" << k << ".rs\"]\nmod part" << k
         << ";\npub use part" << k << "::*;\n";
  }
  for (const auto& row : manifestRows)
  {
    manifest << row.first << '\t' << ident(row.first) << '\t' << row.second
             << "\tpart" << partOf[functionIndex.at(ident(row.first))] << '\n';
  }
  output("src/lib.rs", expandConstructors(lib));
  output("src/generated.rs", code.str());
  for (size_t k = 0; k < numParts; ++k)
  {
    output("src/generated_part" + std::to_string(k) + ".rs",
           "//! Generated functions, module " + std::to_string(k) + " of "
               + std::to_string(numParts)
               + ".\n#[allow(unused_imports)]\nuse super::*;\nuse crate::*;\n"
               + parts[k].str());
  }
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
  // The trace of the generated code (see `d_trace` in the header).
  // `datatype_operators_only`: the program is reached only through the
  // programs that the runtime calls for eo::dt_constructors and
  // eo::dt_selectors.
  const std::set<std::string> reached =
      reachable({"$eo_dt_constructors", "$eo_dt_selectors"});
  bool leftNested = false;
  for (const auto& n : d_leftAssoc)
  {
    leftNested |= d_constructors.count(n) != 0;
  }
  std::map<std::string, std::string> leanOf(manifestRows.begin(),
                                            manifestRows.end());
  std::ostringstream trace;
  trace << "{\n  \"version\": 1,\n  \"parts\": " << numParts
        << ",\n  \"left_nested_lists\": " << (leftNested ? "true" : "false")
        << ",\n  \"embedding_kinds\": {";
  bool firstKind = true;
  for (const auto& pk : d_prefixToMetaKind)
  {
    trace << (firstKind ? "" : ", ") << js(pk.first) << ": "
          << js(metaKindToString(pk.second));
    firstKind = false;
  }
  trace << "},\n  \"programs\": [";
  for (size_t i = 0; i < d_trace.size(); ++i)
  {
    const std::string& n = d_trace[i].first;
    trace << (i == 0 ? "\n" : ",\n") << "    {" << d_trace[i].second
          << ", \"lean\": " << js(leanOf.at(n))
          << ", \"datatype_operators_only\": "
          << (reached.count(n) ? "false" : "true") << "}";
  }
  trace << "\n  ]\n}\n";
  std::string tracePath =
      getOutputPath("plugins/rust_meta/rust_meta_trace_gen.json");
  std::ofstream traceOut(tracePath);
  if (!traceOut || !(traceOut << trace.str()))
  {
    EO_FATAL() << "rust-meta: cannot write " << tracePath;
  }
  for (const char* file : {"cache.rs",
                           "front.rs",
                           "native.rs",
                           "num.rs",
                           "eostring.rs",
                           "bitvec.rs",
                           "lit.rs",
                           "kind.rs",
                           "table.rs"})
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
