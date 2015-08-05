#include "dryad_sl.h"

_(dryad)
void rec_dispose(Node * lst _(out \oset ALL_REACH))
  _(requires sll(lst))
  _(ensures ALL_REACH == \oset_empty())
{
  _(assume mutable_list(lst))
  _(assume lst != NULL ==> \malloc_root(lst))
  _(ghost ALL_REACH = sll_reach(lst))
  if (lst != NULL) {
    Node * n = lst->next;
    free(lst);
    _(ghost ALL_REACH = \oset_diff(ALL_REACH, \oset_singleton(lst)))
    rec_dispose(n _(out ALL_REACH));
  }
}
