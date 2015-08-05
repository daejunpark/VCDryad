#include "dryad_dll_defs_rev.h"
_(logic \bool mutable_list(DLNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
DLNode * dll_mid_delete(DLNode * p)
  _(requires p != NULL)
  _(requires \malloc_root(p))
  _(requires dll(p->next))
  _(requires dll_rev(p->prev))
  _(requires \oset_disjoint(dll_reach(p->next), dll_reach_rev(p->prev)))
  _(ensures \result != NULL)
  _(ensures \malloc_root(\result))
  _(ensures dll(\result->next))
  _(ensures dll_rev(\result->prev))
  _(ensures \oset_disjoint(dll_reach(\result->next), dll_reach_rev(\result->prev)))
  _(ensures p->prev != NULL ==> p->prev->next == p->next)
  _(ensures p->next != NULL ==> p->next->prev == p->prev)
{
  _(assume mutable_list(p))
  _(assume mutable_list(p->next))
  _(assume mutable_list(p->prev))
  DLNode * v = p->next;
  DLNode * u = p->prev;
  if (v != NULL) {
    v->prev = u;
  }
  if (u != NULL) {
    u->next = v;
  }
  return p;
}

_(dryad)
void dll_mid_delete_client(DLNode * p) 
  _(requires p != NULL)
  _(requires \malloc_root(p))
  _(requires dll(p->next))
  _(requires dll_rev(p->prev))
  _(requires \oset_disjoint(dll_reach(p->next), dll_reach_rev(p->prev)))
{
  _(assume mutable_list(p))
  p = dll_mid_delete(p);
  _(assume mutable_list(p))
  free(p);
}
