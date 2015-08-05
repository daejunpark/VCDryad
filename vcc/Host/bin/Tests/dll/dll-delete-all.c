#include "dryad_dll_defs.h"

_(logic \bool mutable_list(DLNode * x) =
  x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
DLNode * dll_delete(DLNode * x, int k) 
  _(requires dll(x))
  _(ensures dll(\result))
  _(ensures  \intset_in(k, \old(dll_keys(x))) ==> (dll_keys(\result) == \intset_diff(\old(dll_keys(x)), \intset_singleton(k))))
  _(ensures !\intset_in(k, \old(dll_keys(x))) ==> (dll_keys(\result) == \old(dll_keys(x))))
{
  _(assume mutable_list(x))
  _(assume x != NULL ==> \malloc_root(x))
  if (x == NULL) {
    return x;
  } else if (x->key == k) {
    DLNode * tmp = dll_delete(x->next, k);
    free(x);
    return tmp;
  } else {
    DLNode * tmp = dll_delete(x->next, k);
    _(assume mutable_list(tmp))
    x->next = tmp;
    if (tmp) tmp->prev = x;
    return x;
  }
}
