#ifndef EXPR_TRIE_H
#define EXPR_TRIE_H

#include <string>
#include "expr.h"
#include "base/check.h"

namespace alfc {

class ExprTrie
{
public:
  ExprTrie() : d_data(nullptr) {}
  /** The children */
  std::map<const ExprValue*, ExprTrie> d_children;
  /** The data at this node */
  ExprValue* d_data;
  /** */
  ExprTrie* get(const std::vector<ExprValue*>& children)
  {
    ExprTrie* et = this;
    for (const ExprValue* e : children)
    {
      et = &(et->d_children[e]);
    }
    return et;
  }
  /** */
  void remove(const std::vector<ExprValue*>& children)
  {
    ExprTrie* et = this;
    ExprTrie* etd = nullptr;
    std::map<const ExprValue*, ExprTrie>::iterator itet;
    std::map<const ExprValue*, ExprTrie>::iterator itetd;
    bool updateEtd = false;
    for (ExprValue* e : children)
    {
      itet = et->d_children.find(e);
      if (updateEtd)
      {
        etd = et;
        itetd = itet;
      }
      Assert (itet!=et->d_children.end());
      updateEtd = (et->d_children.size()>1);
      et = &itet->second;
    }
    if (etd!=nullptr)
    {
      etd->d_children.erase(itetd);
    }
    else
    {
      et->d_data = nullptr;
    }
  }
};

}  // namespace alfc

#endif /* EXPR_TRIE_H */
