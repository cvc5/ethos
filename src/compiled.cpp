#include "type_checker.h"
#include "state.h"

namespace alfc {

void State::run_initialize()
{
}

Expr TypeChecker::run_getTypeInternal(Expr& hdType, const std::vector<Expr>& args, std::ostream* out)
{
  return nullptr;
}

Expr TypeChecker::run_evaluate(Expr& e, Ctx& ctx)
{
  return nullptr;
}

Expr TypeChecker::run_evaluateProgram(const std::vector<Expr>& args, Ctx& ctx)
{
  return nullptr;
}

}
