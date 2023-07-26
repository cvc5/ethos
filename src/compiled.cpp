#include "type_checker.h"
#include "state.h"

namespace alfc {

void State::run_initialize()
{
}

Expr TypeChecker::run_getTypeInternal(Expr& hd, std::vector<Expr>& args, std::ostream* out)
{
  return nullptr;
}

Expr TypeChecker::run_evaluate(Expr& hd, std::vector<Expr>& args)
{
  return nullptr;
}

}
