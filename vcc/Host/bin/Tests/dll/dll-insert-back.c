#include "dryad_dll_defs.h"

_(logic \bool mutable_list(DLNode * x) =
  x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
DLNode * dll_insert_back(DLNode * x, int k)
  _(requires dll(x))
  _(ensures \result != NULL)
  _(ensures  dll(\result))
  _(ensures  dll_keys(\result) == \intset_union(\old(dll_keys(x)), \intset_singleton(k)))
{
  _(assume mutable_list(x))
  if (x == NULL) {
    DLNode * tail = (DLNode *) malloc(sizeof(DLNode));
    _(assume tail != NULL)
    tail->key = k;
    tail->next = NULL;
    tail->prev= x;
    return tail;
  } else {
    DLNode * tmp = dll_insert_back(x->next, k);
    _(assume mutable_list(tmp))
    x->next = tmp;
    tmp->prev = x;
    return x;
  }
}
