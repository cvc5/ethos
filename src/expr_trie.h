#ifndef EXPR_TRIE_H
#define EXPR_TRIE_H

#include <string>
#include "expr.h"

namespace alfc {

class ExprTrie
{
public:
  ExprTrie() {}
  std::map<Expr, ExprTrie> d_children;
  Expr d_data;
};

}  // namespace alfc

#endif /* STATE_H */
