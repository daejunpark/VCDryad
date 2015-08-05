#include "dryad_DLL.h"

_(dryad)
void splice(DLNode * h, DLNode * i)
  _(requires dll(h))
  _(requires dll(i))
  _(requires i != NULL)
  _(requires dll_lseg(h, i))
  _(requires \oset_disjoint(dll_lseg_reach(h, i), dll_reach(i)))
  _(requires \oset_disjoint(dll_lseg_reach(h, i), dll_reach(h)))
  _(requires \oset_disjoint(dll_reach(i), dll_reach(h)))
  _(ensures dll(h))
  _(ensures dll(i))
  _(ensures \oset_disjoint(dll_reach(h), dll_reach(i)))
{ 
  _(assume mutable_list(h))
  DLNode * j;
  if (h != NULL && i != h) 
  {
    j = i->prev;
    i->prev = NULL;
    j->next = NULL;
    i->prev = NULL;
  }
}
