/******************************************************************************
 * This file is part of the ethos project.
 * See COPYING for licensing information.
 ******************************************************************************/
#include "rust_meta_reduce.h"

#include <algorithm>

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
  return rustIdent(name);
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
        lean(parent.lean),
        m(parent.m),
        o(out),
        d_shared(parent.d_shared),
        next(parent.next)
  {
  }
  std::map<Expr, std::string> vars;
  /** Starts the body of another function: no variable is known. */
  void clear() { vars.clear(); }
  /**
   * The proof of what this emitter writes, as a script for Lean: a line
   * for each line of Rust, in the tactics of the proofs' Tactic.lean
   * (pathos, proofs/PathosProofs). `store` counts the stores so far (an
   * operation that may add a term gives a new one), `facts` are the
   * hypotheses about handles, which hold of the current store and are
   * carried over to the next, `pure` those about terms, which no store is
   * part of. Where something is written that the script has no line for
   * yet, `why` says what, and no proof is written for the program.
   */
  struct Lean
  {
    std::vector<std::string> lines;
    size_t store = 0;
    std::vector<std::string> facts;
    std::vector<std::string> pure;
    /** The variables whose terms the code built: never the stuck term. */
    std::set<std::string> built;
    std::string why;
    /** The function of lean-meta's case file for the case being written. */
    std::string caseDef;
    /** The helper functions whose text the proof goes through. */
    std::vector<std::string> unfolds;
    /** The programs called. */
    std::set<std::string> calls;
    /** What the lines being written begin with: they are in a block. */
    std::string indent;
    /** A Rust variable that the Lean has under another name. */
    std::map<std::string, std::string> alias;
    /**
     * The width and value fields of a binary literal that a pattern took
     * apart ("<width> <value>"), and the handle of the literal: building
     * the binary again from them is in range.
     */
    std::map<std::string, std::string> binaryOf;
    /**
     * The variables whose states the proof shows to be OK (`good_tac`, by
     * pathos's Runtime/StateInv.lean): an argument, the tail of an OK
     * state, the empty state, and what a function that keeps states OK
     * builds from OK states.
     */
    std::set<std::string> okState;
    /** The variables whose proofs are `pf F` of a term `F` not stuck. */
    std::set<std::string> okProof;
    /** The formula of a proof argument (`$eo_pf F`), and the argument. */
    std::map<std::string, size_t> pfOf;
    /** The proof arguments whose formula is applied without the guard. */
    std::set<size_t> proofOK;
  };
  Lean lean;
  /**
   * What a call passes for the `j`-th argument of `callee`, which may
   * have to be OK: written once the callee's `good` is known (see
   * `leanProofs`), from whether `v` is a state or a proof the proof
   * shows to be OK.
   */
  std::string leanGood(const std::string& callee,
                       size_t j,
                       const std::string& v) const
  {
    std::string x = ln(v);
    bool ok = lean.okState.count(x) || lean.okProof.count(x);
    return std::string("\x01") + callee + "\x02" + std::to_string(j) + "\x02"
           + (ok ? "1" : "0") + "\x03";
  }
  /** The Lean name of a Rust variable. */
  std::string ln(const std::string& v) const
  {
    auto it = lean.alias.find(v);
    return it == lean.alias.end() ? v : ln(it->second);
  }
  std::string leanStore() const
  {
    return lean.store == 0 ? "s" : "s" + std::to_string(lean.store);
  }
  std::string leanInv() const
  {
    return lean.store == 0 ? "hinv" : "hinv" + std::to_string(lean.store);
  }
  /** That the current store is no deeper in calls than the first. */
  std::string leanRem() const
  {
    return lean.store == 0 ? "hrem" : "(hG.rem hrem)";
  }
  /**
   * Whether the proofs have the lemmas of the constructor `name`
   * (`CtorSpec.<ident>.construct` and `.destruct`), which lean-meta writes
   * with the embedding (pathos's MiniCtors.lean): every constructor the
   * runtime stores as a node over its fields (Embedding::Data in the
   * schema, which is user operators too), of a datatype that the embedding
   * has. lean-meta leaves out the model's datatypes (values, and the maps,
   * sequences and regular languages over values: their reals have no
   * encoding), and the list at the head of its MiniEmbed is the authority:
   * a constructor named here that has no lemma fails the Lean build.
   */
  bool leanHasCtorLemma(const std::string& name) const
  {
    for (const char* special : {"$emb_Stuck",
                                "$emb_Apply",
                                "$emb_Boolean",
                                "$emb_Numeral",
                                "$emb_Rational",
                                "$emb_String",
                                "$emb_Binary"})
    {
      if (name == special)
      {
        return false;
      }
    }
    if (starts(name, "$emb_UOp"))
    {
      return false;
    }
    if (starts(name, "$emb_"))
    {
      std::string prefix = name.substr(5, name.find('.') - 5);
      auto it = m.d_prefixToMetaKind.find(prefix);
      if (prefix == "rsm"
          || (it != m.d_prefixToMetaKind.end()
              && (it->second == MetaKind::SMT_VALUE
                  || it->second == MetaKind::SMT_MAP
                  || it->second == MetaKind::SMT_SEQ)))
      {
        return false;
      }
    }
    return true;
  }
  /** Whether the proof has it that the term of `v` is not stuck. */
  bool leanNotStuck(const std::string& v) const
  {
    std::string x = ln(v);
    return lean.built.count(x)
           || std::find(lean.pure.begin(), lean.pure.end(), "hn_" + x)
                  != lean.pure.end();
  }
  /**
   * `s.apply(f, a)` and its line. Where lean-meta writes logos's guarded
   * application `__eo_mk_apply` (`guarded`: the application is evaluatable,
   * by lean-meta's rule in lean_meta_reduce.cpp), the runtime's `apply` is
   * that one for one (`Store.apply_mk_rep`) and either part may be stuck;
   * otherwise logos writes `Term.Apply`, and the parts must not be stuck
   * (`Store.apply_rep`).
   */
  std::string leanApply(const std::string& f, const std::string& a,
                        bool guarded = false)
  {
    if (guarded)
    {
      std::string st = leanStore(), inv = leanInv();
      std::string v = val("s.apply(" + f + ", " + a + ")?");
      leanStoreStep("Store.apply_mk_rep " + st + " " + ln(f) + " " + ln(a)
                        + " _ _ " + inv + " h64 h_" + ln(f) + " h_" + ln(a),
                    v);
      return v;
    }
    for (const std::string& x : {ln(f), ln(a)})
    {
      // the formula of a proof argument: the program assumes the argument
      // OK (`ProofOK`), which says the formula is not stuck
      auto it = lean.pfOf.find(x);
      if (!leanNotStuck(x) && it != lean.pfOf.end())
      {
        leanLine("have hn_" + x + " := hg_a" + std::to_string(it->second)
                 + " _ rfl");
        lean.pure.push_back("hn_" + x);
        lean.proofOK.insert(it->second);
      }
    }
    if (!leanNotStuck(f) || !leanNotStuck(a))
    {
      // logos builds the application, the store gives the stuck term:
      // the first finding of pathos's docs/proofs.md
      leanUnsupported("an application of a term that may be stuck");
    }
    std::string st = leanStore(), inv = leanInv();
    std::string v = val("s.apply(" + f + ", " + a + ")?");
    lean.built.insert(v);
    leanStoreStep("Store.apply_rep " + st + " " + ln(f) + " " + ln(a)
                      + " _ _ " + inv + " h64 h_" + ln(f) + " h_" + ln(a)
                      + " (by ns_tac) (by ns_tac)",
                  v);
    return v;
  }
  /**
   * The lines of a call of the runtime on a slice of arguments `vs`, whose
   * specification `spec` takes the store, the slice and what it holds,
   * the facts about the arguments, the invariant: the result is `v`.
   */
  void leanArgsStep(const std::string& spec,
                    const std::string& st,
                    const std::string& inv,
                    const std::vector<std::string>& vs,
                    const std::string& v)
  {
    std::string reps;
    for (const std::string& x : vs)
    {
      reps += " h_" + ln(x);
    }
    leanLine("step as ⟨e_" + v + ", he_" + v + "⟩");
    leanStoreStep(spec + " " + st + " e_" + v + " (by rw [he_" + v + "]; rfl)"
                      + reps + " " + inv + " h64",
                  v);
  }
  void leanLine(const std::string& line)
  {
    lean.lines.push_back(lean.indent + line);
  }
  void leanUnsupported(const std::string& what)
  {
    if (lean.why.empty())
    {
      lean.why = what;
    }
  }
  static std::string words(const std::vector<std::string>& list)
  {
    std::string ret;
    for (const std::string& f : list)
    {
      ret += " " + f;
    }
    return ret;
  }
  /** Where a pattern fails: the case ends, with these as its last words. */
  std::string leanElse() const
  {
    return "else " + leanInv() + " hG in " + lean.caseDef;
  }
  /** `unapply` of `value` into the handles `f` and `a`. */
  void leanUnapply(const std::string& value,
                   const std::string& f,
                   const std::string& a)
  {
    leanLine("pat_unapply h_" + ln(value) + " as ⟨" + f + ", " + a + ", x_" + f
             + ", x_" + a + ", h_" + f + ", h_" + a + ", hn_" + f + ", hn_" + a
             + "⟩ using " + leanInv() + " " + leanElse());
    lean.facts.push_back("h_" + f);
    lean.facts.push_back("h_" + a);
    lean.pure.push_back("hn_" + f);
    lean.pure.push_back("hn_" + a);
  }
  /**
   * An operation on the store whose specification is `spec` (a Lean term)
   * and whose result is the variable `v`.
   */
  void leanStoreStep(const std::string& spec, const std::string& v)
  {
    std::string before = words(lean.facts);
    lean.store++;
    leanLine("store_step with " + spec + " as ⟨" + v + ", "
                         + leanStore() + ", " + leanInv() + ", h_" + v
                         + "⟩ growing hG carrying" + before);
    lean.facts.push_back("h_" + v);
  }
  /** `if a != b { return Ok(None) }` on two handles. */
  void leanSame(const std::string& ra, const std::string& rb)
  {
    std::string a = ln(ra), b = ln(rb);
    leanLine("pat_same " + a + " " + b + " with h_" + a + " h_" + b
                         + " using " + leanInv() + " " + leanElse());
  }
  /** What a part of this emitter's text (see the constructor) proved. */
  void leanAdopt(const Emitter& part)
  {
    lean.lines.insert(lean.lines.end(),
                      part.lean.lines.begin() + lean.lines.size(),
                      part.lean.lines.end());
    lean.store = part.lean.store;
    lean.facts = part.lean.facts;
    lean.pure = part.lean.pure;
    lean.built = part.lean.built;
    lean.unfolds = part.lean.unfolds;
    lean.calls = part.lean.calls;
    lean.alias = part.lean.alias;
    lean.okState = part.lean.okState;
    lean.okProof = part.lean.okProof;
    lean.pfOf = part.lean.pfOf;
    lean.proofOK = part.lean.proofOK;
    if (lean.why.empty())
    {
      lean.why = part.lean.why;
    }
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
    lean.unfolds.push_back(name);
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
  /**
   * `name(s, a, b)`, a call of a helper, as Lean has it on the store `st`:
   * `name st a b`.
   */
  std::string leanApplied(const std::string& call, const std::string& st) const
  {
    std::string applied = call.substr(0, call.find('(')) + " " + st;
    for (size_t i = call.find('(') + 2; i < call.size();)
    {
      size_t j = call.find_first_of(",)", i);
      std::string arg = call.substr(i, j - i);
      arg.erase(0, arg.find_first_not_of(' '));
      if (!arg.empty())
      {
        applied += " " + ln(arg);
      }
      i = j + 1;
    }
    return applied;
  }
  std::string conditional(const Expr& c,
                          const Expr& yes,
                          const Expr& no,
                          bool native)
  {
    std::string cv = expr(c);
    // In the proof the conditional is a statement of its own, proved in
    // place, a bullet per branch: its function gives a handle of logos's
    // `__eo_ite` (or `native_ite`) of the condition and the two branches.
    const std::string outerStore = leanStore(), outerInv = leanInv(),
                      outerRem = leanRem(), outerIndent = lean.indent;
    const std::vector<std::string> outerFacts = lean.facts,
                                   outerPure = lean.pure;
    const std::set<std::string> outerBuilt = lean.built;
    const size_t outerStoreCount = lean.store;
    const size_t outerUnfolds = lean.unfolds.size();
    const std::string tag = std::to_string(next);
    const std::string hx = "hx_" + tag, hbv = "hbv_" + tag;
    size_t open = lean.lines.size();
    lean.lines.push_back("");
    lean.lines.push_back("");
    lean.indent = outerIndent + "  ";
    if (lean.store != 0)
    {
      leanLine("have hrem := " + outerRem);
    }
    leanLine("have hG := Store.Grows.refl " + outerStore);
    leanLine(std::string("rcases Store.boolean_value_")
             + (native ? "native" : "term") + " h_" + ln(cv) + " with ⟨" + hx
             + ", " + hbv + "⟩ | ⟨" + hx + ", " + hbv + "⟩"
             + (native ? "" : " | ⟨" + hx + ", " + hbv + "⟩"));
    // a branch: from the store of the call, its lines, its end
    auto branch =
        [&](const Expr& e, std::ostringstream& out, const char* lemma) {
          lean.indent = outerIndent + "  ";
          leanLine("· ite_branch " + hbv);
          lean.indent = outerIndent + "    ";
          Emitter be(*this, out);
          std::string r = be.expr(e);
          next = be.next;
          leanAdopt(be);
          leanLine("ite_done " + leanInv() + " hG with (" + lemma + " _ " + hx
                   + " h_" + ln(r) + ")");
          lean.store = outerStoreCount;
          lean.facts = outerFacts;
          lean.pure = outerPure;
          lean.built = outerBuilt;
          return r;
        };
    std::ostringstream ys, ns;
    std::string a =
        branch(yes, ys, native ? "native_ite_true_rep" : "eo_ite_true_rep");
    std::string b =
        branch(no, ns, native ? "native_ite_false_rep" : "eo_ite_false_rep");
    if (!native)
    {
      lean.indent = outerIndent + "  ";
      leanLine("· ite_branch " + hbv);
      leanLine("  ite_stuck " + outerInv + " hG with " + hx);
    }
    lean.lines.back() += ")";
    lean.indent = outerIndent;
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
    // the helpers that the branches are cut into are unfolded in the block
    std::string unfolds;
    for (size_t i = outerUnfolds; i < lean.unfolds.size(); ++i)
    {
      unfolds += " " + lean.unfolds[i];
    }
    lean.unfolds.resize(outerUnfolds);
    std::string v = fresh();
    lean.lines[open] =
        outerIndent + "have h_ite_" + v + " := (show "
        + leanApplied(call, outerStore) + " ⦃ r s' => s'.Inv ∧ " + outerStore
        + ".Grows s' ∧ match r with | core.result.Result.Ok t => "
          "Represents.rep s' t ("
        + (native ? "SmtEval.native_ite" : "Eo.__eo_ite")
        + " _ _ _) | core.result.Result.Err _ => True ⦄div from by";
    lean.lines[open + 1] =
        outerIndent + "  unfold " + call.substr(0, call.find('(')) + unfolds;
    o << "let " << v << " = " << attempt(call) << ";\n" << CUT;
    leanStoreStep("h_ite_" + v, v);
    return v;
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
      // A function of its own, as a conditional is.
      std::string a = expr(t[start]), b = expr(t[start + 1]);
      // In the proof the requirement is a statement of its own, proved
      // in place: its function gives a handle of logos's `__eo_requires`
      // of the two terms and of what the third argument computes.
      const std::string outerStore = leanStore(), outerInv = leanInv(),
                        outerRem = leanRem(), outerIndent = lean.indent;
      const std::vector<std::string> outerFacts = lean.facts,
                                     outerPure = lean.pure;
      const bool first = lean.store == 0;
      const size_t outerUnfolds = lean.unfolds.size();
      size_t open = lean.lines.size();
      lean.lines.push_back("");
      lean.lines.push_back("");
      lean.indent += "  ";
      if (!first)
      {
        leanLine("have hrem := " + outerRem);
      }
      leanLine("have hG := Store.Grows.refl " + outerStore);
      leanLine("req_same " + ln(a) + " " + ln(b) + " with h_" + ln(a) + " h_"
               + ln(b) + " using " + outerInv + " hG");
      leanLine("req_stuck h_" + ln(a) + " as hq_" + ln(a) + " using " + outerInv
               + " hG");
      std::ostringstream rs;
      Emitter re(*this, rs);
      std::string r = re.expr(t[start + 2]);
      next = re.next;
      leanAdopt(re);
      // (the statement has holes for the three terms, which the proof
      // fills: it is given as a term, whose holes may wait for its proof)
      leanLine("req_done " + leanInv() + " hG with h_" + ln(r) + " using hq_"
               + ln(a) + ")");
      lean.indent = outerIndent;
      lean.facts = outerFacts;
      lean.pure = outerPure;
      std::string body = "if " + a + " != " + b
                         + " { return Ok(s.stuck()); }\nlet stuck = "
                         + attempt("s.is_stuck(" + a + ")")
                         + ";\nif stuck { return Ok(s.stuck()); }\n"
                         + close(rs.str(), "Ok(" + r + ")", "CheckResult<Term>");
      std::string call = helper("requires", {}, body);
      const std::string fn = call.substr(0, call.find('('));
      std::string applied = leanApplied(call, outerStore);
      std::string unfolds;
      for (size_t i = outerUnfolds; i < lean.unfolds.size(); ++i)
      {
        unfolds += " " + lean.unfolds[i];
      }
      lean.unfolds.resize(outerUnfolds);
      std::string v = fresh();
      lean.lines[open] =
          outerIndent + "have h_req_" + v + " := (show " + applied
          + " ⦃ r s' => s'.Inv ∧ " + outerStore
          + ".Grows s' ∧ match r with | core.result.Result.Ok t => "
            "Represents.rep s' t (Eo.__eo_requires _ _ _) | "
            "core.result.Result.Err _ => True ⦄div from by";
      lean.lines[open + 1] = outerIndent + "  unfold " + fn + unfolds;
      o << "let " << v << " = " << attempt(call) << ";\n" << CUT;
      leanStoreStep("h_req_" + v, v);
      return v;
    }
    if (k == Kind::EVAL_EQ || k == Kind::EVAL_LENGTH || k == Kind::EVAL_AND)
    {
      std::vector<std::string> vs;
      std::string as;
      for (size_t i = start; i < t.getNumChildren(); ++i)
      {
        vs.push_back(expr(t[i]));
        as += (i == start ? "" : ", ") + vs.back();
      }
      std::string st = leanStore(), inv = leanInv();
      std::string v =
          val("s.builtin_core(EvalOp::" + evalOp(k) + ", &[" + as + "])?");
      std::string spec = k == Kind::EVAL_EQ       ? "Store.builtin_spec_eq"
                         : k == Kind::EVAL_LENGTH ? "Store.builtin_spec_len"
                                                  : "Store.builtin_spec_and";
      leanArgsStep(spec, st, inv, vs, v);
      return v;
    }
    if (k == Kind::EVAL_NIL || k == Kind::EVAL_CONS)
    {
      std::vector<std::string> vs;
      std::string as;
      for (size_t i = start; i < t.getNumChildren(); ++i)
      {
        vs.push_back(expr(t[i]));
        as += (i == start ? "" : ", ") + vs.back();
      }
      std::string st = leanStore(), inv = leanInv(), rem = leanRem();
      if (k == Kind::EVAL_NIL)
      {
        // a call of the generated `$eo_nil`, which logos's case writes as
        // `__eo_nil` too
        std::string v = val(ident("$eo_nil") + "(s, " + as + ")?");
        std::string spec = "ih." + ident("$eo_nil") + " " + st, holes, reps;
        for (const std::string& x : vs)
        {
          spec += " " + ln(x);
          holes += " _";
          reps += " h_" + ln(x);
        }
        leanStoreStep(spec + holes + " " + inv + " h64 " + rem + reps, v);
        lean.calls.insert("$eo_nil");
        return v;
      }
      // `eo::cons`: pathos's Store.builtin_spec_cons (Runtime/Lists.lean),
      // which takes what is proved of the generated `$eo_is_list_nil`. The
      // element must not be stuck (logos's `__eo_cons` does not catch a
      // stuck element), and the signature must have no operator that nests
      // to the left (the lemma walks right-nested lists)
      bool left = false;
      for (const auto& n : m.d_leftAssoc)
      {
        left |= m.d_constructors.count(n) != 0;
      }
      if (left)
      {
        leanUnsupported("eo::cons with an operator that nests to the left");
      }
      if (vs.size() != 3 || !leanNotStuck(vs[1]))
      {
        leanUnsupported("eo::cons of an element that may be stuck");
      }
      std::string v = val("s.builtin_list(EvalOp::" + evalOp(k) + ", &[" + as + "])?");
      std::string reps;
      for (const std::string& x : vs)
      {
        reps += " h_" + ln(x);
      }
      leanLine("step as ⟨e_" + v + ", he_" + v + "⟩");
      leanStoreStep("Store.builtin_spec_cons n ih." + ident("$eo_is_list_nil") + " " + st
                        + " e_" + v + " (by rw [he_" + v + "]; rfl)" + reps
                        + " (by ns_tac) " + inv + " h64 " + rem + " (fun _ => rfl)",
                    v);
      lean.calls.insert("$eo_is_list_nil");
      return v;
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
      std::string st = leanStore(), inv = leanInv();
      std::string v = val("s.literal(" + literal(t) + ")?");
      // a literal is never the stuck term
      lean.built.insert(v);
      if (k == Kind::BOOLEAN)
      {
        leanStoreStep(std::string("Store.literal_boolean_spec ") + st
                          + (t.getValue()->asLiteral()->d_bool ? " true "
                                                               : " false ")
                          + inv + " h64",
                      v);
      }
      else
      {
        leanUnsupported("a literal that is not a Boolean");
      }
      return v;
    }
    if (t.getNumChildren() == 0)
    {
      if (k == Kind::PARAM)
      {
        EO_FATAL() << "rust-meta: unbound parameter " << t;
      }
      if (k == Kind::PROGRAM_CONST)
      {
        leanUnsupported("a program constant");
        return val(ident(getName(t)) + "(s)?");
      }
      std::string n = k == Kind::TYPE        ? "$emb_Type"
                      : k == Kind::BOOL_TYPE ? "$emb_Bool"
                                             : getName(t);
      std::string st = leanStore(), inv = leanInv();
      std::string v = val("s.construct(" + ctor(n) + ", &[])?");
      // the stuck term is not a node: `construct` gives handle 0
      const bool stuck = n == "$emb_Stuck";
      if (!stuck && !leanHasCtorLemma(n))
      {
        leanUnsupported("the constructor " + n
                        + ", which is not stored as a node (no lemma yet)");
      }
      leanLine("step as ⟨e_" + v + ", he_" + v + "⟩");
      leanStoreStep((stuck ? std::string("Store.construct_stuck_spec ")
                           : "CtorSpec." + ident(n) + ".construct ")
                        + st + " e_" + v
                        + " (by rw [he_" + v + "]; exact empty_args) " + inv
                        + " h64",
                    v);
      lean.built.insert(v);
      if (n == "$emb_s.nil" || n == "$emb_s.Stuck")
      {
        // `StateOK.nil`, `StateOK.stuck`
        lean.okState.insert(v);
      }
      return v;
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
        if (t.getNumChildren() == 2 && (name == "true" || name == "false"))
        {
          std::string st = leanStore(), inv = leanInv();
          std::string v = val(native(name, 0, ""));
          leanStoreStep("Store.native_bool_spec " + st + " " + name + " " + inv
                            + " h64",
                        v);
          return v;
        }
        if (t.getNumChildren() == 2 && !name.empty()
            && name.find_first_not_of("-0123456789") == std::string::npos
            && name.find_first_of("0123456789") != std::string::npos
            && name.size() <= 11)
        {
          // a numeral constant, a value (`Integer::from` of a `u32`,
          // negated if need be): pathos proves it from the specs of `from`
          // and `neg` (Runtime/IntNatives.lean)
          std::string st = leanStore(), inv = leanInv();
          std::string v = val(native(name, 0, ""));
          leanLine("simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, "
                   "num.Integer.toInt_ofInt, Std.bind_ok]");
          leanStoreStep(std::string(name[0] == '-' ? "Store.raw_int_neg_u32_spec "
                                                   : "Store.raw_int_u32_spec ")
                            + st + " " + (name[0] == '-' ? name.substr(1) : name)
                            + "#u32 (" + name + ") (by scalar_tac) " + inv
                            + " h64",
                        v);
          return v;
        }
        if (t.getNumChildren() == 2 && name.size() >= 2 && name.front() == '"'
            && name.back() == '"'
            && name.find_first_of("\\\"", 1) == name.size() - 1
            && std::all_of(name.begin(), name.end(), [](char c) {
                 return c >= ' ' && c <= '~';
               }))
        {
          // a string constant, a value (`raw` of the literal of its code
          // points): pathos proves it stands for logos's string literal
          // (Runtime/StringLits.lean); the text is printable ASCII without
          // escapes, so it reads the same in Lean
          std::string st = leanStore(), inv = leanInv();
          std::string v = val(native(name, 0, ""));
          // the array of code points, then the vector of them
          leanLine("step as ⟨e_" + v + ", he_" + v + "⟩");
          leanLine("simp only [eostring.EoString.from_code_points, Std.bind_ok]");
          leanStoreStep("Store.raw_str_vec_spec " + st + " _ _ rfl " + inv + " h64", v);
          leanLine("replace h_" + ln(v) + " := Represents.rep_of_eq h_" + ln(v)
                   + " (y := SmtEval.native_string_lit " + name
                   + ") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_" + v
                   + "]; decide)");
          return v;
        }
        if (t.getNumChildren() == 2 && name == "nat.zero")
        {
          // the natural number 0 (pathos's Runtime/Nats.lean)
          std::string st = leanStore(), inv = leanInv();
          std::string v = val(native(name, 0, ""));
          leanStoreStep("Store.native_nat_zero_spec " + st + " " + inv + " h64", v);
          return v;
        }
        // the native operations with a specification in the proofs, and
        // its name (pathos's Runtime/Natives.lean, Strings.lean and
        // IntNatives.lean: Store.native_spec_<name>)
        static const std::map<std::string, std::string> specified{
            {"teq", "teq"},
            {"Teq", "Teq"},
            {"streq", "streq"},
            {"and", "and"},
            {"or", "or"},
            {"not", "not"},
            {"string_valid", "string_valid"},
            {"string_prefix_eq", "string_prefix_eq"},
            {"zeq", "zeq"},
            {"zleq", "zleq"},
            {"mod_total", "mod_total"},
            {"int.pow2", "int_pow2"},
            {"int.to_nat", "int_to_nat"},
            {"Int.toNat", "int_to_nat"},
            {"nat.succ", "nat_succ"},
            {"uconst_id", "uconst_id"}};
        if (!specified.count(name))
        {
          leanUnsupported("the native operation " + name);
        }
        std::vector<std::string> vs;
        std::string as;
        for (size_t i = 2; i < t.getNumChildren(); ++i)
        {
          vs.push_back(expr(t[i]));
          as += (i == 2 ? "" : ", ") + vs.back();
        }
        std::string st = leanStore(), inv = leanInv();
        std::string v = val(native(name, t.getNumChildren() - 2, as));
        if (specified.count(name))
        {
          leanArgsStep("Store.native_spec_" + specified.at(name), st, inv, vs, v);
        }
        return v;
      }
      // a numeral, rational or string literal from its native value
      // (pathos's Runtime/Numbers.lean and Runtime/StringLits.lean); other
      // literal constructors have no lemma yet
      const bool number = (n == "$emb_Numeral" || n == "$emb_Rational"
                           || n == "$emb_String")
                          && t.getNumChildren() == 2;
      std::vector<std::string> vs;
      std::string as;
      for (size_t i = 1; i < t.getNumChildren(); ++i)
      {
        vs.push_back(expr(t[i]));
        as += (i == 1 ? "" : ", ") + vs.back();
      }
      // a binary literal from the width and value that a pattern took from
      // one, so they are in range (pathos's Runtime/StringLits.lean)
      std::string binary;
      if (n == "$emb_Binary" && vs.size() == 2)
      {
        auto it = lean.binaryOf.find(ln(vs[0]) + " " + ln(vs[1]));
        if (it != lean.binaryOf.end())
        {
          binary = it->second;
        }
      }
      if (!number && binary.empty() && !leanHasCtorLemma(n))
      {
        leanUnsupported("the constructor " + n
                        + " with arguments, which is not stored as a node");
      }
      std::string st = leanStore(), inv = leanInv();
      std::string v = val("s.construct(" + ctor(n) + ", &[" + as + "])?");
      std::string reps;
      for (const std::string& x : vs)
      {
        reps += " h_" + ln(x);
      }
      leanLine("step as ⟨e_" + v + ", he_" + v + "⟩");
      leanStoreStep((number ? std::string(n == "$emb_Numeral"
                                              ? "Store.construct_numeral_spec "
                                          : n == "$emb_Rational"
                                              ? "Store.construct_rational_spec "
                                              : "Store.construct_string_spec ")
                     : !binary.empty() ? std::string("Store.construct_binary_spec ")
                                       : "CtorSpec." + ident(n) + ".construct ")
                        + st + " e_" + v
                        + " (by rw [he_" + v + "]; rfl)" + reps
                        + (binary.empty()
                               ? std::string()
                               : " (Store.rep_binary_okBv h_" + binary + ")")
                        + " " + inv + " h64",
                    v);
      lean.built.insert(v);
      if (n == "$eo_pf" && vs.size() == 1 && leanNotStuck(vs[0]))
      {
        // `ProofOK.pf`
        lean.okProof.insert(v);
      }
      return v;
    }
    if (k == Kind::APPLY && t[0].getKind() == Kind::PROGRAM_CONST)
    {
      std::string n = getName(t[0]);
      Kind b = builtin(n);
      if (b != Kind::NONE)
      {
        if (b != Kind::EVAL_REQUIRES && b != Kind::EVAL_EQ)
        {
          leanUnsupported("the builtin " + n);
        }
        return op(b, t, 1);
      }
      std::vector<std::string> vs;
      std::string as;
      for (size_t i = 1; i < t.getNumChildren(); ++i)
      {
        vs.push_back(expr(t[i]));
        as += (i == 1 ? "" : ", ") + vs.back();
      }
      std::string st = leanStore(), inv = leanInv(), rem = leanRem();
      std::string v = val(ident(n) + "(s" + (as.empty() ? "" : ", " + as) + ")?");
      std::string spec = "ih." + ident(n) + " " + st, holes, reps, goods;
      for (size_t j = 0; j < vs.size(); ++j)
      {
        const std::string& x = vs[j];
        spec += " " + ln(x);
        holes += " _";
        reps += " h_" + ln(x);
        goods += leanGood(n, j, x);
      }
      leanStoreStep(spec + holes + " " + inv + " h64 " + rem + reps + goods, v);
      lean.calls.insert(n);
      // the functions that keep states OK (pathos's Runtime/StateInv.lean):
      // the state arguments that must be OK for the result to be
      static const std::map<std::string, std::vector<size_t>> keeps = {
          {"$eo_push_proven", {1}},
          {"$eo_invoke_cmd_check_proven", {0}},
          {"$eo_invoke_cmd_step_pop", {1}},
          {"$eo_invoke_cmd", {0}},
          {"$eo_invoke_cmd_list", {0}},
          {"$eo_invoke_assume_list", {0}}};
      auto kt = keeps.find(n);
      if (kt != keeps.end())
      {
        bool ok = true;
        for (size_t j : kt->second)
        {
          ok = ok && j < vs.size() && lean.okState.count(ln(vs[j]));
        }
        if (ok)
        {
          lean.okState.insert(v);
        }
      }
      if (n == "$eo_state_proven_nth" && vs.size() == 2
          && lean.okState.count(ln(vs[0])))
      {
        // the formula of an OK state's element is not stuck
        leanLine("have hn_" + v + " := state_proven_nth_ne_stuck_of h_" + v
                 + " (by good_tac)");
        lean.pure.push_back("hn_" + v);
      }
      return v;
    }
    if (isLiteralOp(k))
    {
      // `eo::ite` is a conditional (see `conditional`), `eo::requires` a
      // function of its own, and `eo::eq`, `eo::len` and `eo::and` have
      // their specs; the others have none
      if (k != Kind::EVAL_REQUIRES && k != Kind::EVAL_EQ
          && k != Kind::EVAL_IF_THEN_ELSE && k != Kind::EVAL_LENGTH
          && k != Kind::EVAL_AND && k != Kind::EVAL_NIL && k != Kind::EVAL_CONS)
      {
        leanUnsupported("a builtin operator");
      }
      return op(k, t, 0);
    }
    if (k == Kind::FUNCTION_TYPE)
    {
      // `(-> T U)` is `((FunType T) U)`: the constant `$emb_FunType` (its
      // generated `construct` lemma), then two applications, as an
      // application term has. Where lean-meta writes them guarded
      // (`__eo_mk_apply`, for an evaluatable function type), the runtime's
      // `apply` is that one for one (`Store.apply_mk_rep`); otherwise
      // `Store.apply_rep`.
      if (!leanHasCtorLemma("$emb_FunType"))
      {
        leanUnsupported("a function type");
      }
      size_t n = t.getNumChildren();
      const bool guarded = n == 2 && t.isEvaluatable();
      std::string tail = expr(t[n - 1]);
      for (size_t i = n - 1; i > 0; --i)
      {
        std::string a = expr(t[i - 1]);
        std::string st = leanStore(), inv = leanInv();
        std::string h = val(named("$emb_FunType", ""));
        leanLine("step as ⟨e_" + h + ", he_" + h + "⟩");
        leanStoreStep("CtorSpec." + ident("$emb_FunType") + ".construct " + st
                          + " e_" + h + " (by rw [he_" + h
                          + "]; exact empty_args) " + inv + " h64",
                      h);
        lean.built.insert(h);
        tail = leanApply(leanApply(h, a, guarded), tail, guarded);
      }
      return tail;
    }
    if (k == Kind::APPLY && t.getNumChildren() == 2)
    {
      std::string f = expr(t[0]), a = expr(t[1]);
      return leanApply(f, a, t.isEvaluatable());
    }
    if (k == Kind::VARIABLE)
    {
      leanUnsupported("a variable term");
      std::string as = args(t, 0);
      return val(named("$emb_Var", as));
    }
    EO_FATAL() << "rust-meta: unsupported expression " << t << " (" << k << ")";
    return "";
  }
  void pattern(const Expr& t, const std::string& value)
  {
    Kind k = t.getKind();
    if (k == Kind::PARAM)
    {
      auto it = vars.find(t);
      if (it != vars.end())
      {
        o << "if " << value << " != " << it->second << fail << CUT;
        leanSame(value, it->second);
      }
      else
      {
        vars[t] = value;
      }
      return;
    }
    if (k == Kind::FUNCTION_TYPE && t.getNumChildren() == 2)
    {
      // `(-> T U)` is `(FunType T) U` as applications, whose head the store
      // keeps as the node of `$emb_FunType`
      std::string outer = part("s.unapply(" + value + ")?");
      std::string f = fresh(), r = fresh();
      o << "let Some((" << f << ", " << r << ")) = " << outer << " else" << fail
        << ";\n"
        << CUT;
      leanUnapply(value, f, r);
      std::string inner = part("s.unapply(" + f + ")?");
      std::string op = fresh(), l = fresh();
      o << "let Some((" << op << ", " << l << ")) = " << inner << " else"
        << fail << ";\n"
        << CUT;
      leanUnapply(f, op, l);
      std::string fun = part("s.is_node(" + op + ", "
                            + m.constructorOption("$emb_FunType") + ")?");
      o << "if !" << fun << fail << CUT;
      leanLine("pat_is_node h_" + ln(op) + " : x_" + ln(op)
               + " is Eo.Term.FunType by Embed.inv_Term_FunType " + leanElse());
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
      leanUnapply(value, f, a);
      pattern(t[0], f);
      pattern(t[1], a);
      return;
    }
    if (k == Kind::APPLY_OPAQUE || k == Kind::VARIABLE)
    {
      size_t start = k == Kind::VARIABLE ? 0 : 1;
      std::string n = k == Kind::VARIABLE ? "$emb_Var" : getName(t[0]);
      std::string found;
      bool data = false;
      std::string native;
      if (starts(n, "$native_apply_"))
      {
        native = getName(t[1]);
        // `nat.zero` and `(nat.succ m)` have specs (pathos's
        // Runtime/Nats.lean); the others not yet
        if (!((native == "nat.zero" && t.getNumChildren() == 2)
              || (native == "nat.succ" && t.getNumChildren() == 3)))
        {
          leanUnsupported("a native pattern");
        }
        found = part(nativePattern(native, value));
        start = 2;
      }
      else
      {
        found = part("s.destruct(" + ctor(n) + ", " + value + ")?");
        data = true;
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
      if (native == "nat.zero" || native == "nat.succ")
      {
        // the pattern stores a numeral (0, or the predecessor), so the
        // store changes
        std::string st = leanStore(), inv = leanInv();
        std::string before = words(lean.facts);
        lean.store++;
        if (native == "nat.zero")
        {
          leanLine("pat_native_zero Store.native_pattern_nat_zero_spec " + st + " "
                   + ln(value) + " h_" + ln(value) + " " + inv + " h64 storing ⟨"
                   + leanStore() + ", " + leanInv() + "⟩ growing hG carrying"
                   + before + " in " + lean.caseDef);
        }
        else
        {
          const std::string& f = fields[0];
          leanLine("pat_destruct_lit Store.native_pattern_succ_spec " + st + " "
                   + ln(value) + " h_" + ln(value) + " " + inv + " h64 as ⟨" + f
                   + ", x_" + f + ", h_" + f + "⟩ storing ⟨" + leanStore() + ", "
                   + leanInv() + "⟩ growing hG carrying" + before + " in "
                   + lean.caseDef);
          lean.facts.push_back("h_" + f);
        }
      }
      else if (data && fields.size() == 1
               && (n == "$emb_Boolean" || n == "$emb_Numeral"
                   || n == "$emb_Rational" || n == "$emb_String"))
      {
        // a Boolean, numeral, rational or string literal: destruct stores a
        // native copy of its value (pathos's Runtime/Literals.lean,
        // Runtime/Numbers.lean and Runtime/StringLits.lean), so the store
        // changes
        std::string spec = n == "$emb_Boolean"    ? "Store.destruct_boolean_spec"
                           : n == "$emb_Numeral"  ? "Store.destruct_numeral_spec"
                           : n == "$emb_Rational" ? "Store.destruct_rational_spec"
                                                  : "Store.destruct_string_spec";
        std::string st = leanStore(), inv = leanInv();
        std::string before = words(lean.facts);
        lean.store++;
        const std::string& f = fields[0];
        leanLine("pat_destruct_lit " + spec + " " + st + " "
                 + ln(value) + " h_" + ln(value) + " " + inv + " h64 as ⟨" + f
                 + ", x_" + f + ", h_" + f + "⟩ storing ⟨" + leanStore() + ", "
                 + leanInv() + "⟩ growing hG carrying" + before + " in "
                 + lean.caseDef);
        lean.facts.push_back("h_" + f);
      }
      else if (data && fields.size() == 2 && n == "$emb_Binary")
      {
        // a binary literal: destruct stores its width and its value as two
        // numerals (pathos's Runtime/StringLits.lean)
        std::string st = leanStore(), inv = leanInv();
        std::string before = words(lean.facts);
        lean.store++;
        const std::string& f = fields[0];
        const std::string& g = fields[1];
        leanLine("pat_destruct_lit2 Store.destruct_binary_spec " + st + " "
                 + ln(value) + " h_" + ln(value) + " " + inv + " h64 as ⟨" + f
                 + ", x_" + f + ", h_" + f + "⟩ ⟨" + g + ", x_" + g + ", h_" + g
                 + "⟩ storing ⟨" + leanStore() + ", " + leanInv()
                 + "⟩ growing hG carrying" + before + " in " + lean.caseDef);
        lean.facts.push_back("h_" + f);
        lean.facts.push_back("h_" + g);
        lean.binaryOf[f + " " + g] = ln(value);
      }
      else if (data && !leanHasCtorLemma(n))
      {
        leanUnsupported("the constructor " + n
                        + " in a pattern, which is not stored as a node");
      }
      else if (data)
      {
        std::string line = "pat_destruct CtorSpec." + ident(n) + ".destruct h_"
                           + ln(value) + " as";
        for (const std::string& f : fields)
        {
          line += " ⟨" + f + ", x_" + f + ", h_" + f + "⟩";
          lean.facts.push_back("h_" + f);
        }
        leanLine(line + " " + leanElse());
        std::string x = ln(value);
        if (n == "$emb_s.cons" && fields.size() == 2 && lean.okState.count(x))
        {
          // the tail of an OK state (`StateOK.tail`)
          lean.okState.insert(fields[1]);
        }
        if (n == "$eo_pf" && fields.size() == 1 && x.size() > 1 && x[0] == 'a'
            && x.find_first_not_of("0123456789", 1) == std::string::npos)
        {
          lean.pfOf[fields[0]] = std::stoul(x.substr(1));
        }
      }
      for (size_t i = start; i < t.getNumChildren(); ++i)
      {
        pattern(t[i], fields[i - start]);
      }
      return;
    }
    if (isLiteral(k) || t.getNumChildren() == 0)
    {
      std::string expected = expr(t);
      o << "if " << value << " != " << expected << fail << CUT;
      leanSame(value, expected);
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
    // The proof is written by hand (pathos's Runtime/StateNth.lean): the
    // lookup with jump pointers against logos's recursive function, from
    // what is proved of `$eo_StateObj_proven`
    d_leanProofs.emplace_back();
    LeanProof& lp = d_leanProofs.back();
    lp.name = name;
    lp.nargs = 2;
    // the state is assumed OK, as every state is
    lp.good = {"StateOK", ""};
    lp.calls = {"$eo_StateObj_proven"};
    lp.handProof = "state_proven_nth_spec n (fun m hm => (ih m hm)."
                   + ident("$eo_StateObj_proven") + ")";
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
      // The proof of the fold is written by hand (pathos's
      // Runtime/AssumeFold.lean, invoke_assume_list_spec) for the guard
      // `(eo::and ($eo_is_bool_type F) ($eo_is_closed F))` and the push
      // `$eo_push_input_assume_check`, from what is proved of those three.
      const Expr f = step[2][1];
      auto isCall = [&](const Expr& x, const char* prog) {
        return x.getKind() == Kind::APPLY && x.getNumChildren() == 2
               && x[0].getKind() == Kind::PROGRAM_CONST
               && getName(x[0]) == prog && x[1] == f;
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
      if (isAnd && isCall(g[g0], "$eo_is_bool_type")
          && isCall(g[g0 + 1], "$eo_is_closed")
          && getName(body[0]) == "$eo_push_input_assume_check" && body[2] == f)
      {
        d_leanProofs.emplace_back();
        LeanProof& lp = d_leanProofs.back();
        lp.name = name;
        lp.nargs = 2;
        // the state is assumed OK, as every state is
        lp.good = {"StateOK", ""};
        lp.calls = {"$eo_is_bool_type", "$eo_is_closed",
                    "$eo_push_input_assume_check"};
        auto spec = [&](const char* prog) {
          return "(fun m hm => (ih m hm)." + ident(prog) + ")";
        };
        lp.handProof = "invoke_assume_list_spec n " + spec("$eo_is_bool_type") + " "
                       + spec("$eo_is_closed") + " "
                       + spec("$eo_push_input_assume_check");
      }
      return out.str();
    }
  }
  d_leanProofs.emplace_back();
  LeanProof& proof = d_leanProofs.back();
  proof.name = name;
  proof.nargs = nargs;
  proof.good.assign(nargs, "");
  for (size_t i = 0; i < nargs; ++i)
  {
    // every state is assumed OK (pathos's Runtime/StateInv.lean)
    std::ostringstream ts;
    ts << ty[i];
    if (ts.str() == "($native_embed_checker \"CState\")")
    {
      proof.good[i] = "StateOK";
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
    proof.why = "a constant, not a program with cases";
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
          proof.stuck.push_back(i);
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
  // for the proof: the cases each entry of `level` tries, and whether it
  // is a case or a group
  std::vector<LeanProof::Member> members;
  for (size_t c = 0; c < ncases; ++c)
  {
    level.push_back("case_" + std::to_string(c) + "_" + id);
    members.push_back({level.back(), c, c + 1, true});
  }

  for (size_t depth = 0; level.size() > groupSize; ++depth)
  {
    std::vector<std::string> above;
    std::vector<LeanProof::Member> aboveMembers;
    for (size_t g = 0; g * groupSize < level.size(); ++g)
    {
      std::string group = "cases_" + std::to_string(depth) + "_"
                          + std::to_string(g) + "_" + id;
      above.push_back(group);
      LeanProof::Group pg;
      pg.name = group;
      for (size_t c = g * groupSize;
           c < level.size() && c < (g + 1) * groupSize;
           ++c)
      {
        pg.members.push_back(members[c]);
      }
      pg.lo = pg.members.front().lo;
      pg.hi = pg.members.back().hi;
      proof.groups.push_back(pg);
      aboveMembers.push_back({group, pg.lo, pg.hi, false});
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
  }
  proof.top = members;
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
    const std::string caseDef = "EoCases." + leanName(name) + ".case_"
                                + std::to_string(c);
    e.lean.caseDef = caseDef;
    for (size_t j = 0; j < nargs; ++j)
    {
      e.lean.facts.push_back("h_a" + std::to_string(j));
    }
    for (size_t j : proof.stuck)
    {
      e.lean.pure.push_back("hn_a" + std::to_string(j));
    }
    for (size_t j = 0; j < nargs; ++j)
    {
      if (proof.good[j] == "StateOK")
      {
        e.lean.okState.insert("a" + std::to_string(j));
      }
    }
    for (size_t j = 0; j < nargs; ++j)
    {
      e.pattern(pat[j + 1], "a" + std::to_string(j));
    }
    std::string value, last;
    if (loop && tailCall(body))
    {
      // Every argument is evaluated before the next round has any.
      value = "Next::Again([";
      std::string reps;
      size_t goods = 0;
      for (size_t j = 1; j <= nargs; ++j)
      {
        std::string v = e.expr(body[j]);
        value += (j == 1 ? "" : ", ") + v;
        reps += " h_" + e.ln(v);
        if (proof.good[j - 1] == "StateOK")
        {
          // the next round's state is OK, as this round's is
          goods++;
          if (!e.lean.okState.count(e.ln(v)))
          {
            e.leanUnsupported("a state that may not be OK");
          }
        }
      }
      value += "])";
      last = "case_again " + e.leanInv() + " hG with" + reps
             + (goods == 0 ? "" : " goods " + std::to_string(goods));
    }
    else
    {
      std::string v = e.expr(body);
      value = loop ? "Next::Done(" + v + ")" : v;
      last = "case_done " + e.leanInv() + " hG with h_" + e.ln(v);
    }
    out << e.close(cs.str(), "Ok(Some(" + value + "))", ret) << "}\n";
    // The proof of the case.
    LeanProof::Case pc;
    pc.unfolds = Emitter::words(e.lean.unfolds);
    pc.lines = e.lean.lines;
    pc.lines.push_back(last + " in " + caseDef + " using"
                       + Emitter::words(e.lean.pure));
    for (size_t j : e.lean.proofOK)
    {
      proof.good[j] = "ProofOK";
      if (loop && e.lean.why.empty())
      {
        // the next round would have to be shown OK too
        e.leanUnsupported("a loop whose proof argument is assumed OK");
      }
    }
    pc.why = e.lean.why;
    proof.cases.push_back(pc);
    proof.calls.insert(e.lean.calls.begin(), e.lean.calls.end());
    if (proof.why.empty() && !e.lean.why.empty())
    {
      proof.why = "case " + std::to_string(c) + " has " + e.lean.why;
    }
  }
  if (proof.why.empty() && cases)
  {
    // where no case applies, the body gives the stuck term; lemma C gives
    // the stuck value (HasStuck) for terms, proofs and native Booleans, and
    // otherwise `default` (every logos type is Inhabited): logos writes no
    // default case for such a type, so its cases cover every value and the
    // proof shows that the body never gets there
    Expr rt = ty[nargs];
    MetaKind rk = getTypeMetaKindFor(rt, MetaKind::EUNOIA, true);
    std::ostringstream rs;
    rs << rt;
    proof.split = rk != MetaKind::EUNOIA && rk != MetaKind::PROOF;
    if (proof.split && rs.str() != "($native_type_0 \"Bool\")")
    {
      proof.noCase = "default";
    }
  }
  if (proof.why.empty() && cases)
  {
    // the lemma that logos's function is the body's takes that each
    // argument is a value a store can hold (Valid), which the proofs have
    // for terms and proofs, and as `True` for the types below
    // (Runtime/Embed.lean says why that is enough)
    static const std::set<std::string> validTypes = {
        "($native_type_0 \"Bool\")",
        "($native_type_0 \"String\")",
        "($native_type_0 \"Nat\")",
        "($native_embed_checker \"CState\")",
        "($native_embed_checker \"CStateObj\")",
        "($native_embed_checker \"CArgList\")",
        "($native_embed_checker \"CCmdList\")",
        "($native_embed_checker \"CIndexList\")",
        "$eo_Rule",
        "($native_embed_eo \"Datatype\")",
        "($native_embed_eo \"DatatypeCons\")",
        "($native_embed_eo \"DatatypeDecl\")",
        "$smt_Type",
        "($native_embed_smt \"SmtDatatype\")",
        "($native_embed_smt \"SmtDatatypeCons\")",
        "($native_embed_smt \"SmtDatatypeDecl\")",
        "$eo_Cmd",
        "$smt_Term"};
    for (size_t i = 0; i < nargs && proof.why.empty(); ++i)
    {
      MetaKind ak = getTypeMetaKindFor(ty[i], MetaKind::EUNOIA, true);
      std::ostringstream as;
      as << ty[i];
      if (ak != MetaKind::EUNOIA && ak != MetaKind::PROOF
          && validTypes.count(as.str()) == 0)
      {
        proof.why =
            "an argument of a type that has no Valid in the proofs "
            "yet (lemma C)";
      }
    }
  }
  proof.loop = loop;
  // pathos's Store.Ops: typeSemId
  proof.cache = cache == CacheKind::NONE      ? ""
                : cache == CacheKind::PROGRAM ? std::to_string(d_programIds.at(name))
                : cache == CacheKind::EO_TYPE ? "4294967296"
                                              : "4294967297";
  proof.typeKind = cache == CacheKind::EO_TYPE    ? "Eunoia"
                   : cache == CacheKind::SMT_TYPE ? "Smt"
                                                  : "";
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

std::string RustMetaReduce::leanName(const std::string& name)
{
  std::string lean = replace_all(name, "-", "_");
  if (lean == "end" || lean == "variable")
  {
    return "__eo_" + lean;
  }
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
  return lean;
}

static std::string list_of(size_t n)
{
  std::string ret;
  for (size_t i = 0; i < n; ++i)
  {
    ret += (i == 0 ? "a" : ", a") + std::to_string(i);
  }
  return ret;
}

void RustMetaReduce::leanProofs(size_t numParts) const
{
  // A program has a proof if each of its cases has a script and each
  // program it calls has a proof.
  std::map<std::string, std::string> why;
  for (const LeanProof& p : d_leanProofs)
  {
    why[p.name] = d_leanHas.count(p.name)
                      ? p.why
                      : "no logos function: only the runtime's datatype "
                        "operators reach it";
  }
  // What a call passes for an argument its callee assumes OK (see
  // `leanGood`): `good_tac`'s proof, where the line's emitter named where
  // the argument comes from, and otherwise the reason there is no proof.
  std::map<std::string, const std::vector<std::string>*> goodOf;
  for (const LeanProof& p : d_leanProofs)
  {
    goodOf[p.name] = &p.good;
  }
  auto resolve = [&](const std::string& line, std::string* reason) {
    std::string out;
    size_t i = 0;
    for (size_t b; (b = line.find('\x01', i)) != std::string::npos;)
    {
      size_t m1 = line.find('\x02', b), m2 = line.find('\x02', m1 + 1),
             e = line.find('\x03', m2);
      out += line.substr(i, b - i);
      std::string callee = line.substr(b + 1, m1 - b - 1);
      size_t j = std::stoul(line.substr(m1 + 1, m2 - m1 - 1));
      bool ok = line[m2 + 1] == '1';
      auto it = goodOf.find(callee);
      std::string g =
          it != goodOf.end() && j < it->second->size() ? (*it->second)[j] : "";
      if (!g.empty())
      {
        out += " (by good_tac)";
        if (!ok && reason != nullptr && reason->empty())
        {
          *reason = g == "StateOK" ? "a state that may not be OK"
                                   : "a proof that may not be OK";
        }
      }
      i = e + 1;
    }
    return out + line.substr(i);
  };
  for (const LeanProof& p : d_leanProofs)
  {
    for (size_t c = 0; c < p.cases.size() && why[p.name].empty(); ++c)
    {
      std::string reason;
      for (const std::string& l : p.cases[c].lines)
      {
        resolve(l, &reason);
      }
      if (!reason.empty())
      {
        why[p.name] = "case " + std::to_string(c) + " has " + reason;
      }
    }
  }
  for (bool changed = true; changed;)
  {
    changed = false;
    for (const LeanProof& p : d_leanProofs)
    {
      if (!why[p.name].empty())
      {
        continue;
      }
      for (const std::string& c : p.calls)
      {
        auto it = why.find(c);
        if (it == why.end() || !it->second.empty())
        {
          why[p.name] = "it calls " + c + ", which has no proof";
          changed = true;
          break;
        }
      }
    }
  }
  std::ostringstream o, table;
  table << "source\tproof\twhy\n";
  o << "module\npublic import $CHECKER$\npublic import $CALC$.Logos\n"
       "import all $CALC$.Logos\npublic import $CALC$.SmtTranslate\n"
       "import all $CALC$.SmtTranslate\npublic import $CALC$.SmtModel\n"
       "import all $CALC$.SmtModel\npublic import $CASES$\nimport all $CASES$\n"
       "public import PathosProofs.Generated\n\n"
       "/-!\n# The proofs about the generated functions\n\n"
       "Written by Ethos's rust-meta with the functions: for each program, "
       "that its\nRust computes what logos's function of the same name does. "
       "Do not edit.\n-/\n\n"
       "set_option linter.unusedVariables false\n"
       "set_option maxRecDepth 8000\n\n"
       "@[expose] public section\n\nnamespace pathos_compiled_checker\n\n"
       "open Aeneas Aeneas.Std Result\nopen Eo hiding Term\nopen Smtm\n"
       "open generated";
  for (size_t k = 0; k < numParts; ++k)
  {
    o << " generated.part" << k;
  }
  o << "\n\n";
  const std::string ok = "core.result.Result.Ok", err = "core.result.Result.Err";
  struct Names
  {
    std::string id, lean, handles, terms, binders, reps, xs, as, valid, valids;
    /** What is assumed of the arguments beside their handles (`good`):
     * as hypotheses, as their names, and as the premises of `Spec`. */
    std::string goodBinders, goods, goodPremises;
  };
  auto names = [&](const LeanProof& p) {
    Names n;
    n.id = ident(p.name);
    // logos's function, by its name: Logos.lean has it in Eo, the modules
    // of the SMT translation and model at the top (both are opened)
    n.lean = leanName(p.name);
    for (size_t i = 0; i < p.nargs; ++i)
    {
      std::string a = "a" + std::to_string(i);
      n.as += " " + a;
      n.xs += " x_" + a;
      n.terms += " (x_" + a + " : _)";
      n.reps += " h_" + a;
      n.binders += " (h_" + a + " : Represents.rep s " + a + " x_" + a + ")";
      n.valid += " (hw_" + a + " : Valid.valid x_" + a + ")";
      n.valids += " (by valid_tac hinv h_" + a + ")";
      if (i < p.good.size() && !p.good[i].empty())
      {
        n.goodBinders += " (hg_" + a + " : " + p.good[i] + " x_" + a + ")";
        n.goods += " hg_" + a;
        n.goodPremises += " " + p.good[i] + " x_" + a + " →";
      }
    }
    n.handles = p.nargs == 0 ? "" : " (" + n.as.substr(1) + " : Term)";
    return n;
  };
  std::vector<const LeanProof*> proved;
  for (const LeanProof& p : d_leanProofs)
  {
    table << p.name << '\t' << (why[p.name].empty() ? "generated" : "none")
          << '\t' << why[p.name] << '\n';
    if (why[p.name].empty())
    {
      proved.push_back(&p);
    }
  }
  // What is proved of each program, and all of it together: a program's
  // proof uses what is proved of the programs it calls, itself among
  // them, at a smaller number of calls that may still be entered.
  for (const LeanProof* p : proved)
  {
    Names n = names(*p);
    o << "/-- What is proved of `" << p->name << "`. -/\ndef " << n.id
      << ".Spec (n : Nat) : Prop :=\n  ∀ (s : Store)" << n.handles << n.terms
      << ", s.Inv → Platform64 → s.remaining ≤ n →\n   ";
    for (size_t i = 0; i < p->nargs; ++i)
    {
      o << " Represents.rep s a" << i << " x_a" << i << " →";
    }
    o << n.goodPremises << "\n    " << n.id << " s" << n.as
      << " ⦃ r s' => s'.Inv ∧ s.Grows s' ∧\n      match r with\n      | " << ok
      << " t => Represents.rep s' t (" << n.lean << n.xs << ")\n      | " << err
      << " _ => True ⦄div\n\n";
  }
  o << "/-- What is proved of the programs, for stores that can enter `n` "
       "more calls. -/\nstructure Specs (n : Nat) : Prop where\n";
  for (const LeanProof* p : proved)
  {
    o << "  " << ident(p->name) << " : " << ident(p->name) << ".Spec n\n";
  }
  o << "\n";
  for (const LeanProof* p : proved)
  {
    Names n = names(*p);
    if (!p->handProof.empty())
    {
      o << "/-- `" << p->name << "`, by the proof written by hand. -/\ntheorem "
        << n.id << "_spec (n : Nat) (ih : ∀ m < n, Specs m) : " << n.id
        << ".Spec n :=\n  " << p->handProof << "\n\n";
      continue;
    }
    const std::string head = " (n : Nat) (ih : Specs n) (s : Store)" + n.handles
                             + n.terms
                             + "\n    (hinv : s.Inv) (h64 : Platform64) (hrem : "
                               "s.remaining ≤ n)"
                             + n.binders + n.goodBinders;
    std::string stuck, facts, notStuck;
    for (size_t i : p->stuck)
    {
      stuck += " (hn_a" + std::to_string(i) + " : x_a" + std::to_string(i)
               + " ≠ Eo.Term.Stuck)";
      facts += " hn_a" + std::to_string(i);
    }
    notStuck = facts;
    const std::string post = " ⦃ r s' => s'.Inv ∧ s.Grows s' ∧\n      match r with\n";
    // the arguments of the next round of a loop
    std::string next, list;
    for (size_t i = 0; i < p->nargs; ++i)
    {
      std::string k = std::to_string(i);
      next += " (u" + k + " : Term) (y" + k + " : _)";
      list += (i == 0 ? "u" : ", u") + k;
    }
    std::string again = "∃" + next + ", arr.val = [" + list + "]";
    std::string ys;
    for (size_t i = 0; i < p->nargs; ++i)
    {
      std::string k = std::to_string(i);
      again += " ∧ Represents.rep s' u" + k + " y" + k;
      ys += " y" + k;
    }
    for (size_t i = 0; i < p->nargs; ++i)
    {
      // the next round's states are OK (a loop assumes no proof OK)
      if (p->good[i] == "StateOK")
      {
        again += " ∧ StateOK y" + std::to_string(i);
      }
    }
    std::string defs, cds;
    for (size_t c = 0; c < p->cases.size(); ++c)
    {
      const std::string cd = "EoCases." + leanName(p->name) + ".case_"
                             + std::to_string(c);
      const std::string fn = "case_" + std::to_string(c) + "_" + n.id;
      defs += " " + cd;
      cds += (c == 0 ? "" : ", ") + cd + n.xs;
      o << "theorem " << fn << "_spec" << head << stuck << " :\n    " << fn
        << " s" << n.as << post;
      if (p->loop)
      {
        o << "      | " << ok << " (some (Next.Done t)) =>\n        ∃ res, " << cd
          << n.xs << " = some res ∧ Represents.rep s' t res\n      | " << ok
          << " (some (Next.Again arr)) =>\n        " << again << " ∧\n          "
          << cd << n.xs << " = some (" << n.lean << ys << ")\n";
      }
      else
      {
        o << "      | " << ok << " (some t) =>\n        ∃ res, " << cd << n.xs
          << " = some res ∧ Represents.rep s' t res\n";
      }
      o << "      | " << ok << " none => " << cd << n.xs << " = none\n      | "
        << err << " _ => True ⦄div := by\n  unfold " << fn
        << p->cases[c].unfolds << "\n  have hG := Store.Grows.refl s\n";
      for (const std::string& l : p->cases[c].lines)
      {
        o << "  " << resolve(l, nullptr) << "\n";
      }
      o << "\n";
    }
    // The groups of cases: a group answers what the first of its cases
    // that answers does, or none of them answers.
    auto leaves = [&](size_t lo, size_t hi) {
      std::string l = "[";
      for (size_t c = lo; c < hi; ++c)
      {
        l += (c == lo ? "" : ", ") + std::string("EoCases.") + leanName(p->name)
             + ".case_" + std::to_string(c) + n.xs;
      }
      return l + "]";
    };
    auto names = [&](size_t lo, size_t hi) {
      std::string l;
      for (size_t c = lo; c < hi; ++c)
      {
        l += (c == lo ? "" : ", ") + std::string("hl_") + std::to_string(c);
      }
      return l;
    };
    // the facts that the cases [lo, hi) answered none
    auto noneFacts = [&](size_t lo, size_t hi) {
      std::string l;
      for (size_t c = lo; c < hi; ++c)
      {
        l += " hl_" + std::to_string(c);
      }
      return l;
    };
    // `group_step` for the member `m` of a whole that tries the cases
    // [lo, hi), from the k-th store
    auto groupStep = [&](const LeanProof::Member& m,
                         size_t lo,
                         size_t hi,
                         size_t k,
                         const std::string& extra,
                         bool body) {
      std::string sk = k == 0 ? "" : std::to_string(k);
      std::string pat = "⟨" + names(m.lo, m.hi) + "⟩";
      // in a loop, a member answers the end of the loop or its next round
      const std::string tac = std::string(body ? "body_group" : "group")
                              + (p->loop ? "_round_step" : "_step");
      return "  " + tac + " with "
             + m.name + "_spec n ih s" + sk + n.as + n.xs + " hinv" + sk
             + " h64 " + (k == 0 ? "hrem" : "(hG.rem hrem)") + n.reps + n.goods
             + notStuck
             + "\n    as ⟨s" + std::to_string(k + 1) + ", hinv"
             + std::to_string(k + 1) + ", hc" + std::to_string(k)
             + "⟩ growing hG carrying" + n.reps
             + (body && p->loop ? " hbud" : "") + "\n    split (show "
             + leaves(lo, hi) + " = " + leaves(lo, m.lo) + " ++ "
             + leaves(m.lo, m.hi) + " ++ " + leaves(m.hi, hi)
             + " from rfl)\n    otherwise " + pat + " using" + extra
             + noneFacts(lo, m.lo) + "\n";
    };
    for (const LeanProof::Group& g : p->groups)
    {
      const std::string& fn = g.name;
      o << "theorem " << fn << "_spec" << head << stuck << " :\n    " << fn
        << " s" << n.as << post;
      if (p->loop)
      {
        o << "      | " << ok << " (some (Next.Done t)) =>\n        ∃ res, (∀ d, "
          << "firstSome " << leaves(g.lo, g.hi)
          << " d = res) ∧ Represents.rep s' t res\n      | " << ok
          << " (some (Next.Again arr)) =>\n        " << again
          << " ∧\n          ∀ d, firstSome " << leaves(g.lo, g.hi) << " d = "
          << n.lean << ys << "\n";
      }
      else
      {
        o << "      | " << ok << " (some t) =>\n        ∃ res, (∀ d, firstSome "
          << leaves(g.lo, g.hi) << " d = res) ∧ Represents.rep s' t res\n";
      }
      o << "      | " << ok << " none =>";
      for (size_t c = g.lo; c < g.hi; ++c)
      {
        o << (c == g.lo ? " " : " ∧ ") << "EoCases." << leanName(p->name)
          << ".case_" << c << n.xs << " = none";
      }
      o << "\n      | " << err << " _ => True ⦄div := by\n  unfold " << fn
        << "\n  have hG := Store.Grows.refl s\n";
      size_t k = 0;
      for (const LeanProof::Member& m : g.members)
      {
        // a member is passed the facts that the arguments are not stuck,
        // as the group is
        o << groupStep(m, g.lo, g.hi, k, facts, false);
        ++k;
      }
      o << "  group_none hinv" << k << " hG with "
        << (g.hi - g.lo == 1 ? names(g.lo, g.hi)
                             : "⟨" + names(g.lo, g.hi) + "⟩")
        << "\n\n";
    }
    // what the body computes, in the functions of the cases
    o << "/-- logos's `" << leanName(p->name)
      << "` is what the generated body does: the tests for the stuck term,\n"
         "then the first case that answers. -/\ntheorem "
      << n.id << ".rust_eq" << n.terms << n.valid << " :\n    " << n.lean << n.xs
      << " =\n      (";
    for (size_t i : p->stuck)
    {
      o << "if x_a" << i << " = Eo.Term.Stuck then HasStuck.stuck else ";
    }
    o << "firstSome [" << cds << "] " << p->noCase << ") := by\n  conv => lhs; unfold "
      << n.lean << "\n  unfold" << defs
      << "\n  logos_eq\n\n";
    // the body: for a loop, a round of it
    const std::string round = (p->loop ? "step_" : "body_") + n.id;
    o << "theorem " << round << "_spec" << head << " :\n    " << round << " s"
      << n.as << post;
    if (p->loop)
    {
      // a round that goes round again has used up some of the budget of
      // calls (its `tick`): the measure of the induction over the loop
      o << "      | " << ok << " (Next.Done t) => Represents.rep s' t (" << n.lean
        << n.xs << ")\n      | " << ok << " (Next.Again arr) =>\n        "
        << "s'.budget < s.budget ∧ " << again << " ∧\n          " << n.lean << n.xs << " = " << n.lean << ys
        << "\n";
    }
    else
    {
      o << "      | " << ok << " t => Represents.rep s' t (" << n.lean << n.xs
        << ")\n";
    }
    o << "      | " << err << " _ => True ⦄div := by\n  rw [" << n.id
      << ".rust_eq" << n.xs << n.valids << "]\n  unfold " << round
      << "\n  have hG := Store.Grows.refl s\n";
    size_t store = 0;
    auto st = [&]() { return store == 0 ? "" : std::to_string(store); };
    // for a type but terms and proofs, the proof that no case fails to
    // apply may split on the arguments
    const std::string splitting = p->split ? " splitting" + n.xs : "";
    if (p->loop)
    {
      store++;
      o << "  tick_step as ⟨s1, hinv1⟩ growing hG carrying" << n.reps << "\n";
    }
    for (size_t i : p->stuck)
    {
      o << "  stuck_check h_a" << i << " : x_a" << i << " as hn_a" << i
        << " else hinv" << st() << " hG\n";
    }
    if (!p->groups.empty())
    {
      // the body tries the top groups
      std::string hn = facts;
      for (const LeanProof::Member& m : p->top)
      {
        o << groupStep(m, 0, p->cases.size(), store, hn, true);
        store++;
      }
      o << "  " << (p->loop ? "round_stuck" : "body_stuck") << " hinv" << st()
        << " hG using" << hn << noneFacts(0, p->cases.size()) << " in" << defs
        << splitting << "\n\n";
    }
    for (size_t c = 0; p->groups.empty() && c < p->cases.size(); ++c)
    {
      o << "  " << (p->loop ? "round_step" : "case_step") << " with case_" << c
        << "_" << n.id << "_spec n ih s" << st() << n.as << n.xs << " hinv"
        << st() << " h64 " << (store == 0 ? "hrem" : "(hG.rem hrem)") << n.reps
        << n.goods << notStuck << "\n    as ⟨s" << store + 1 << ", hinv" << store + 1 << ", hc"
        << c << "⟩ growing hG carrying" << n.reps << (p->loop ? " hbud" : "")
        << " using" << facts << "\n";
      facts += " hc" + std::to_string(c);
      store++;
    }
    if (p->groups.empty())
    {
      o << "  " << (p->loop ? "round_stuck" : "body_stuck") << " hinv" << st()
        << " hG using" << facts << " in" << defs << splitting << "\n\n";
    }
    const std::string result = "      | " + ok + " t => Represents.rep s' t ("
                               + n.lean + n.xs + ")\n      | " + err
                               + " _ => True ⦄div";
    if (p->loop)
    {
      // the loop, by induction over it
      std::string order = n.as + " s" + n.xs;
      o << "theorem body_" << n.id << "_spec" << head << " :\n    body_" << n.id
        << " s" << n.as << post << result << " := by\n";
      // by induction on the budget of calls, which every round that goes
      // round again uses up (its `tick`), over the loop's equation: a loop
      // that Aeneas puts in a block with the programs it calls has no
      // fixpoint induction of its own
      std::ostringstream motive;
      motive << "∀ (k : Nat)" << n.handles << " (s : Store)" << n.terms
             << ", s.budget ≤ k → s.Inv → s.remaining ≤ n →\n     ";
      for (size_t i = 0; i < p->nargs; ++i)
      {
        motive << " Represents.rep s a" << i << " x_a" << i << " →";
      }
      motive << n.goodPremises;
      // stated of the body, whose arguments are in the Rust's order (Aeneas
      // orders the loop function's arguments its own way); the body is the loop
      motive << "\n      body_" << n.id << " s" << n.as << post << result;
      o << "  refine (?_ : " << motive.str() << ") s.budget" << order
        << " le_rfl hinv hrem" << n.reps << n.goods << "\n  intro k\n"
        << "  refine Nat.strong_induction_on k ?_\n  intro k ihl" << order
        << " hk hinv hrem" << n.reps << n.goods << "\n  unfold body_" << n.id
        << " body_"
        << n.id << "_loop"
        << "\n  step with step_" << n.id << "_spec n ih s" << n.as << n.xs
        << " hinv h64 hrem" << n.reps << n.goods
        << " as ⟨r, s1, hinv1, hg1, hr⟩\n  cases r with\n"
           "  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; "
           "exact ⟨hinv1, hg1, trivial⟩\n  | Ok nx =>\n    cases nx with\n"
           "    | Done value =>\n      simp only [WP.dspec_ok, "
           "WP.uncurry'_pair]\n      exact ⟨hinv1, hg1, hr⟩\n"
           "    | Again next =>\n      obtain ⟨hlt, ";
      std::string us, bs, ys2, hreps;
      for (size_t i = 0; i < p->nargs; ++i)
      {
        std::string k = std::to_string(i);
        o << "u" << k << ", y" << k << ", ";
        bs += " b" + k;
        ys2 += " y" + k;
        hreps += ", hrep" + k;
      }
      for (size_t i = 0; i < p->nargs; ++i)
      {
        if (p->good[i] == "StateOK")
        {
          hreps += ", hgood" + std::to_string(i);
        }
      }
      o << "hnext" << hreps << ", heq⟩ := hr\n      simp only\n"
           "      have hlen : next.length = " << p->nargs
        << " := by simp [Array.length, hnext]\n";
      for (size_t i = 0; i < p->nargs; ++i)
      {
        std::string k = std::to_string(i);
        o << "      step as ⟨b" << k << ", hb" << k << "⟩\n      obtain rfl : b"
          << k << " = u" << k << " := by simp [hb" << k << ", hnext]\n";
      }
      std::string hs2 = hreps;
      for (char& ch : hs2)
      {
        if (ch == ',')
        {
          ch = ' ';
        }
      }
      // the rest of the loop, by the hypothesis on the body, which is the
      // loop function with Aeneas's order of the arguments
      o << "      have hrec := ihl s1.budget (by omega)" << bs << " s1" << ys2
        << " le_rfl hinv1 (hg1.rem hrem)" << hs2 << "\n      unfold body_" << n.id
        << " at hrec\n      apply WP.dspec_mono hrec\n      loop_close hg1 heq\n\n";
    }
    // the program: the body between `enter` and `leave`
    std::string congr, xlist, replist = "List.Forall₂.nil", mono = replist;
    for (size_t i = 0; i < p->nargs; ++i)
    {
      congr += " (by congr_one h_a" + std::to_string(i) + " hn)";
      xlist += (i == 0 ? "x_a" : ", x_a") + std::to_string(i);
    }
    for (size_t i = p->nargs; i > 0; --i)
    {
      std::string h = "h_a" + std::to_string(i - 1);
      replist = "(List.Forall₂.cons (Store.Rep.congr " + h + " hn) " + replist
                + ")";
      mono = "(List.Forall₂.cons (Rep.mono hpre " + h + ") " + mono + ")";
    }
    const std::string fpost = "(fun s' t => Represents.rep s' t (" + n.lean
                              + n.xs + "))";
    o << "theorem " << n.id << "_spec (n : Nat) (ih : ∀ m < n, Specs m) : "
      << n.id << ".Spec n := by\n  intro s" << n.as << n.xs << " hinv h64 hrem"
      << n.reps << n.goods << "\n  unfold " << n.id << "\n  apply WP.dspec_mono (Store."
      << (p->cache.empty() ? "framed s hinv hrem"
          : !p->typeKind.empty()
              ? "framed_type_cached s hinv hrem h64 cache.TypeCacheKind."
                    + p->typeKind + " a0"
              : "framed_cached s hinv hrem " + p->cache + "#u32 _ ["
                    + list_of(p->nargs) + "] rfl")
      << "\n    (fun s1 => body_" << n.id << " s1" << n.as << ") " << fpost
      << "\n    (by intro _ _ _ hn h; congr_one h hn)\n";
    if (!p->cache.empty())
    {
      // what the cache says of the program is what is proved of it
      std::string bs, ys, hb, subst, as, hput;
      for (size_t i = 0; i < p->nargs; ++i)
      {
        std::string k = std::to_string(i);
        bs += "b" + k + ", ";
        ys += "y" + k + ", ";
        hb += ", hb" + k;
        subst += "      obtain rfl := Rep.functional hb" + k
                 + " (Represents.congr h_a" + k + " hn)\n";
        as += "a" + k + ", ";
        hput += ", Rep.mono hpre h_a" + k;
      }
      o << "    (by\n      intro s1 res hn hsem\n      obtain ⟨" << bs << ys
        << "hargs" << hb << ", hr⟩ := ProgramSem.of_" << p->cache << " hsem\n"
        << (p->nargs == 0
                ? ""
                : "      simp only [List.cons.injEq, and_true] at hargs\n"
                  "      obtain ⟨"
                      + std::string(p->nargs == 1 ? "" : "") +
                      [&]() {
                        std::string r;
                        for (size_t i = 0; i < p->nargs; ++i)
                        {
                          r += (i == 0 ? "rfl" : ", rfl");
                        }
                        return r;
                      }()
                      + "⟩ := hargs\n")
        << subst
        << "      exact hr)\n    (by\n      intro s1 res hpre h\n"
           "      exact ProgramSem.to_"
        << p->cache << " ⟨" << as << xlist << (p->nargs == 0 ? "" : ", ")
        << "rfl" << hput << ", h⟩)\n";
    }
    o << "    (fun s1 m hinv1 hn hm hrem1 => by\n      spec_exact body_" << n.id
      << "_spec m (ih m hm) s1" << n.as << n.xs << " hinv1 h64 hrem1" << congr
      << n.goods << "))\n  rintro ⟨r, s'⟩ h\n  cases r <;> simpa [WP.uncurry'_pair] using h\n\n";
  }
  o << "/-- **Every program with a generated proof computes what logos's "
       "function does.** -/\ntheorem specs (n : Nat) : Specs n := by\n"
       "  induction n using Nat.strong_induction_on with\n  | _ n ih =>\n"
       "    exact ⟨";
  for (size_t i = 0; i < proved.size(); ++i)
  {
    o << (i == 0 ? "" : ",\n      ") << ident(proved[i]->name) << "_spec n ih";
  }
  o << "⟩\n\nend pathos_compiled_checker\n";
  output("proofs.lean", o.str());
  output("proofs.tsv", table.str());
  // What an entry of the cache of results says, for each program that has
  // the cache: the store's invariant is stated with it.
  std::ostringstream c, conj, mono, lemmas;
  c << "module\npublic import $CHECKER$\npublic import $CALC$.Logos\n"
       "public import $CALC$.SmtTranslate\npublic import $CALC$.SmtModel\n"
       "public import PathosProofs.Store.Rep\n\n"
       "/-!\n# What the cache of program results holds\n\n"
       "Written by Ethos's rust-meta with the functions: for each program "
       "whose results\nare cached, that an entry's result is the program's on "
       "the entry's arguments.\nDo not edit.\n-/\n\n"
       "@[expose] public section\n\nnamespace pathos_compiled_checker\n\n"
       "open Aeneas Aeneas.Std Result\nopen Eo hiding Term\nopen Smtm\n\n";
  std::vector<std::pair<size_t, const LeanProof*>> cached;
  for (const LeanProof& p : d_leanProofs)
  {
    if (!p.cache.empty() && why[p.name].empty())
    {
      cached.emplace_back(std::stoull(p.cache), &p);
    }
  }
  std::sort(cached.begin(), cached.end());
  std::string path;
  for (const auto& e : cached)
  {
    const LeanProof& p = *e.second;
    // an entry: handles of the arguments, which stand for values of the
    // program's argument types, and a handle of the program's result on
    // them
    std::string as, xs, ex, reps, hs, monoArgs;
    for (size_t i = 0; i < p.nargs; ++i)
    {
      std::string k = std::to_string(i);
      as += (i == 0 ? "a" : ", a") + k;
      xs += " x" + k;
      ex += " (a" + k + " : Term)";
      reps += " ∧ Rep nodes a" + k + ".val x" + k;
      hs += ", h" + k;
      monoArgs += ", Rep.mono hpre h" + k;
    }
    for (size_t i = 0; i < p.nargs; ++i)
    {
      ex += " (x" + std::to_string(i) + " : _)";
    }
    std::string names;
    for (size_t i = 0; i < p.nargs; ++i)
    {
      names += "a" + std::to_string(i) + ", ";
    }
    for (size_t i = 0; i < p.nargs; ++i)
    {
      names += "x" + std::to_string(i) + ", ";
    }
    c << "/-- `" << p.name << "`. -/\ndef ProgramSem.p" << p.cache
      << " (nodes : List TermData) (args : List Term) (res : Term) : Prop :=\n "
         " "
      << (p.nargs == 0 ? "" : "∃" + ex + ", ") << "args = [" << as << "]"
      << reps << " ∧\n    Rep nodes res.val (" << leanName(p.name) << xs
      << ")\n\ntheorem ProgramSem.p" << p.cache
      << ".mono {nodes nodes' : List TermData} {args : List Term} {res : "
         "Term}\n"
         "    (hpre : nodes <+: nodes') (h : ProgramSem.p"
      << p.cache << " nodes args res) :\n    ProgramSem.p" << p.cache
      << " nodes' args res := by\n  obtain ⟨" << names << "hargs" << hs
      << ", hr⟩ := h\n  exact ⟨" << names << "hargs" << monoArgs
      << ", Rep.mono hpre hr⟩\n\n";
    conj << "  (pid = " << p.cache << " → ProgramSem.p" << p.cache
         << " nodes args res) ∧\n";
    mono << "fun e => ProgramSem.p" << p.cache << ".mono hpre (h" << path
         << ".1 e), ";
    lemmas << "theorem ProgramSem.of_" << p.cache
           << " {nodes : List TermData} {args : List Term} {res : Term}\n"
              "    (h : ProgramSem nodes "
           << p.cache << " args res) : ProgramSem.p" << p.cache
           << " nodes args res :=\n  h" << path << ".1 rfl\n\n"
              "theorem ProgramSem.to_"
           << p.cache
           << " {nodes : List TermData} {args : List Term} {res : Term}\n"
              "    (h : ProgramSem.p"
           << p.cache << " nodes args res) : ProgramSem nodes " << p.cache
           << " args res := by\n  unfold ProgramSem\n"
              "  refine ⟨";
    for (size_t i = 0; i < cached.size(); ++i)
    {
      lemmas << "?_, ";
    }
    lemmas << "trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by "
              "decide)\n\n";
    path += ".2";
  }
  c << "/-- What an entry of the program `pid` with the arguments `args` and "
       "the result\n`res` says, in a store whose terms are `nodes`. -/\n"
       "def ProgramSem (nodes : List TermData) (pid : Nat) (args : List Term) "
       "(res : Term) : Prop :=\n"
    << conj.str() << "  True\n\ntheorem ProgramSem.mono {nodes nodes' : List "
                     "TermData} {pid : Nat} {args : List Term}\n"
                     "    {res : Term} (hpre : nodes <+: nodes') (h : "
                     "ProgramSem nodes pid args res) :\n"
                     "    ProgramSem nodes' pid args res :=\n  ⟨"
    << mono.str() << "trivial⟩\n\n"
    << lemmas.str() << "end pathos_compiled_checker\n";
  output("cache_sem.lean", c.str());
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
  // The datatype operators are programs that the runtime calls for
  // eo::dt_constructors and eo::dt_selectors. A signature whose programs
  // use neither has them in its Rust and not in logos's Lean.
  for (const std::string& n :
       reachable({"$eo_dt_constructors", "$eo_dt_selectors"}))
  {
    d_leanHas.insert(n);
  }
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
    size_t before = d_leanProofs.size();
    collect(emitProgram(n, d_programs.at(n)));
    if (d_leanProofs.size() == before)
    {
      d_leanProofs.emplace_back();
      d_leanProofs.back().name = n;
      d_leanProofs.back().why = "compiled to a function of the runtime";
    }
    manifestRows.emplace_back(n, leanName(n));
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
  leanProofs(numParts);
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
