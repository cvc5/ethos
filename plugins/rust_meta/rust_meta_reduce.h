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
  std::set<std::string> reachable() const;
  void selectCaches(const std::set<std::string>& names);
  /** Whether a constructor is a user symbol, not an embedding or meta one. */
  static bool isUserConstructor(const std::string& name);
  std::string schema() const;
  /** The constructors by name, for the runtime's front part. */
  std::string constructorNames() const;
  /** `Some(Constructor::X)` for a constructor of the signature, else `None`. */
  std::string constructorOption(const std::string& name) const;
  /** A runtime template with each `@ctor:NAME@` replaced by that. */
  std::string expandConstructors(std::string text) const;
  std::string emitProgram(const std::string& name, const Program& p);
  void output(const std::string& file, const std::string& text) const;
  static std::string ident(const std::string& name);
  static std::string quote(const std::string& text);
  static std::string literal(const Expr& e);
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
