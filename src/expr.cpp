#include "expr.h"

namespace atc {

ExprValue::ExprValue() : d_kind(Kind::NONE){}

ExprValue::ExprValue(Kind k,
      const std::vector<std::shared_ptr<ExprValue>>& children) : d_kind(k), d_children(children){}
ExprValue::~ExprValue() {}

bool ExprValue::isNull() const { return d_kind==Kind::NONE; }
  
Kind ExprValue::getKind() const { return d_kind; }

const std::vector<std::shared_ptr<ExprValue>>& ExprValue::getChildren() const { return d_children; }

void ExprValue::printDebug(std::ostream& os) const
{
  // TODO
}

std::shared_ptr<ExprValue> ExprValue::getType()
{
  return nullptr;
}
  
std::ostream& operator<<(std::ostream& out, const ExprValue& e)
{
  e.printDebug(out);
  return out;
}

}  // namespace atc

