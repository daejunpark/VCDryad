#include "dryad_dll_defs.h"

_(logic \bool mutable_list(DLNode * x) =
  x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
DLNode * dll_insert_front(DLNode * x, int k) 
  _(requires dll(x))
  _(ensures  dll(\result))
  _(ensures  dll_keys(\result) == \intset_union(\old(dll_keys(x)), \intset_singleton(k)))
{
  _(assume mutable_list(x))
  if (x == NULL) {
    DLNode * head = (DLNode *) malloc(sizeof(DLNode));
    _(assume head != NULL)
    head->key = k;
    head->next = NULL;
    head->prev = NULL;
    return head;
  } else {
    DLNode * head = (DLNode *) malloc(sizeof(DLNode));
    _(assume head != NULL)
    head->key = k;
    head->next = x;
    x->prev = head;
    return head;
  }
}


