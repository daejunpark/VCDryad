#include "dryad_dll_lseg_defs.h"

_(logic \bool mutable_list(DLNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
DLNode * g_list_prepend(DLNode * list, int data, DLNode * p) 
  _(requires dll(list))
  _(requires p != NULL ==> p->next == list)
  _(requires list != NULL ==> list->prev == p)
  _(requires !\oset_in(p, dll_reach(list)))
  _(ensures dll(\result))
  _(ensures \result != NULL)
  _(ensures \result->prev == p && \result->next == list)
  _(ensures p != NULL ==> p->next == \result)
  _(ensures list != NULL ==> list->prev == \result)
  _(ensures dll_keys(\result) == \intset_union(\old(dll_keys(list)), \intset_singleton(data)))
{
  _(assume mutable_list(list))
  _(assume mutable_list(p))
  DLNode * ret = (DLNode *) malloc(sizeof(DLNode));
  _(assume ret != NULL)
  ret->key = data;
  ret->next = list;
  ret->prev = p;
  if (list != NULL) {
    list->prev = ret;
  }
  if (p != NULL) {
     p->next = ret;
  }
  return ret;
}
