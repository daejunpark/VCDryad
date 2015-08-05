#include "dryad_dll_defs_rev.h"
_(logic \bool mutable_list(DLNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
DLNode * dll_mid_insert(DLNode * u, DLNode * v, int k)
  _(requires dll(v))
  _(requires dll_rev(u))
  _(requires \oset_disjoint(dll_reach(v), dll_reach_rev(u)))
  _(ensures \result != NULL)
  _(ensures dll(\result))
  _(ensures dll_keys(\result) == \intset_union(\old(dll_keys(v)), \intset_singleton(k)))
  _(ensures dll_rev(u))
  _(ensures dll_keys_rev(u) == \old(dll_keys_rev(u)))
  _(ensures \oset_disjoint(dll_reach(\result), dll_reach_rev(u)))
{
  _(assume mutable_list(u))
  _(assume mutable_list(v))
  DLNode * r = (DLNode *) malloc(sizeof(DLNode)); 
  _(assume r != NULL)
  r->key = k;
  r->prev = u;
  r->next = v;
  if (u != NULL) {
    u->next = r;
  }
  if (v != NULL) {
    v->prev = r;
  }
  return r;
}
