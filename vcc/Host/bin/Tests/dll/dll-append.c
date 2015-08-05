#include "dryad_dll_defs.h"

_(logic \bool mutable_list(DLNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
DLNode * dll_append(DLNode * x1, DLNode * x2) 
  _(requires dll(x1))
  _(requires dll(x2))
  _(requires \oset_disjoint(dll_reach(x1), dll_reach(x2)))
  _(ensures dll(\result))
  _(ensures dll_keys(\result) == \intset_union(\old(dll_keys(x1)), \old(dll_keys(x2))))
{
  _(assume mutable_list(x1))
  _(assume mutable_list(x2))
  if (x1 == NULL) {
    return x2;
  } else {
    DLNode * tmp = dll_append(x1->next, x2);
    _(assume mutable_list(tmp))
    x1->next = tmp;
    if (tmp) tmp->prev = x1;
    return x1;
  }
}
