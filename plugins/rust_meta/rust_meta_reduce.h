/******************************************************************************
 * This file is part of the ethos project.
 * See COPYING for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_RUST_META_REDUCE_H
#define PLUGIN_RUST_META_REDUCE_H

#include "../meta_reduce_plugin.h"

namespace ethos {

/**
 * Emit a standalone, parser-free Rust proof checker. Structural desugaring
 * supplies calculus-specific typing and command invocation. Builtin operators
 * are compiled to the native Rust runtime instead of their EO implementations.
 */
class RustMetaReduce : public MetaReducePlugin
{
 public:
  explicit RustMetaReduce(State& s);
  void defineProgram(const Expr& v, const Expr& prog) override;
  void define(const std::string& name, const Expr& e) override;
  bool echo(const std::string& msg) override;
  void finalize() override;

 private:
  struct Program
  {
    Expr symbol;
    Expr body;
    bool isDefine;
  };
  struct Constructor
  {
    size_t arity;
  };
  enum class CacheKind
  {
    NONE,
    EO_TYPE,
    SMT_TYPE,
    PROGRAM
  };
  class Emitter;
  bool isBuiltinMetaSymbol(const std::string& name) const override;
  void finalizeDecl(const Expr& e) override;
  /** The programs reached from the roots, but for those in `without`. */
  std::set<std::string> reachable(
      const std::set<std::string>& without = {}) const;
  void selectCaches(const std::set<std::string>& names);
  /** Whether a constructor is a user symbol, not an embedding or meta one. */
  static bool isUserConstructor(const std::string& name);
  std::string schema() const;
  /** The constructors by name, for the runtime's front part. */
  std::string constructorNames() const;
  /**
   * The number that stands for `text` in the calls of generated code: a
   * name or a constant the runtime is given only to read or to report.
   */
  size_t nativeText(const std::string& text);
  std::vector<std::string> d_nativeTexts;
  /** `Some(Constructor::X)` for a constructor of the signature, else `None`. */
  std::string constructorOption(const std::string& name) const;
  /** A runtime template with each `@ctor:NAME@` replaced by that. */
  std::string expandConstructors(std::string text) const;
  std::string emitProgram(const std::string& name, const Program& p);
  /**
   * The trace of the generated code: for each program, in the order
   * written, its name and its entry, as JSON fields. `finalize` writes it
   * to rust_meta_trace_gen.json, beside the crate in the output directory,
   * for consumers that relate the Rust to another rendering of the
   * programs (a proof that the Rust computes what lean-meta's Lean does).
   * It records what was generated, and nothing of what a consumer makes of
   * it. Version 1:
   *
   * - top level: `parts` (the modules `generated::part<k>`),
   *   `left_nested_lists` (a constructor of the signature nests to the
   *   left), `embedding_kinds` (the meta kind of each `$emb_<prefix>.`),
   *   `programs`.
   * - a program: `name`, `id` (its Rust function), `lean` (lean-meta's
   *   name for it), `cache` (`kind`: none, program with its `id`,
   *   eo_type, smt_type), `datatype_operators_only`, `args` and `ret`
   *   (the type as written and its meta kind) for a program with cases,
   *   and `kind`:
   *   - `define`: a constant;
   *   - `state_nth`: compiled to the runtime's state_nth; `calls`;
   *   - `assume_fold`: compiled to a fold; `guard_calls` (the two programs
   *     whose conjunction on the element is the guard, or null), `push`;
   *   - `cases`: `loop` (a tail call is the next round), `stuck` (the
   *     arguments the body tests for the stuck term), `groups` (each with
   *     `name`, the cases [`lo`, `hi`) and `members`, in the order
   *     written), `top` (what the body tries), and `cases`: per case the
   *     nodes of its `patterns`, of its `body` or of the arguments of the
   *     next round (`again`), and its `helpers` (the functions its text
   *     is cut into, in order).
   * - a node of `expr`: `op` (param, literal, program_const, constant (a
   *   constructor without arguments), construct, native, builtin, call,
   *   funtype, apply, variable, max_code_point (`eo::max_code_point`, the
   *   numeral `MAX_CODE_POINT`)) and what it names:
   *   the `kind` and `bool` of a literal, `ctor`, the native's `name` and
   *   `nargs`, the builtin's `eval` and `program`, the callee `program`,
   *   `guarded` (lean-meta writes the application with `__eo_mk_apply`),
   *   the `rounds` of a function type; a conditional (`ite`: eo or native)
   *   or a requirement is a function: `fn`, `args`, `next_var`. `v` is the
   *   variable of the value, `sub` the nodes of the parts, `helpers` as
   *   for a case.
   * - a node of `pattern`: `value` (the variable matched), `pat` (param,
   *   same with the `other` variable, funtype with `f r op l`, apply with
   *   `f a`, ctor with `ctor` or native with `name`, and their `fields`,
   *   value), and `sub`.
   */
  std::vector<std::pair<std::string, std::string>> d_trace;
  void output(const std::string& file, const std::string& text) const;
  static std::string ident(const std::string& name);
  static std::string quote(const std::string& text);
  static Kind builtin(const std::string& name);
  std::map<std::string, Constructor> d_constructors;
  std::vector<std::string> d_constructorOrder;
  std::map<std::string, Program> d_programs;
  std::set<std::string> d_leftAssoc;
  std::map<std::string, CacheKind> d_cacheKinds;
  std::map<std::string, size_t> d_programIds;
};

}  // namespace ethos
#endif
