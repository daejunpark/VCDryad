#include "dryad_sl.h"

_(dryad)
Node * rec_traverse(Node * lst)
  _(requires sll(lst))
  _(ensures  sll(lst))
  _(ensures sll_reach(lst) == \old(sll_reach(lst)))
{
  _(assume mutable_list(lst))
  if (lst != NULL) {
    Node * n = lst->next;
    rec_traverse(n);
  }
}
