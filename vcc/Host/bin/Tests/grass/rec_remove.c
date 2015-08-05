#include "dryad_sl.h"

_(dryad)
Node * rec_remove(Node * lst)
  _(requires sll(lst))
  _(ensures sll(\result))
{
  _(assume mutable_list(lst))
  _(assume lst != NULL ==> \malloc_root(lst))
  int nondet;
  if (lst == NULL) {
    return NULL;
  } else if (nondet) {
    Node * n = lst->next;
    free(lst);
    return n;
  } else {
    Node * n1 = lst->next;
    Node * n2 = rec_remove(n1);
    lst->next = n2;
    return lst;
  }
}
