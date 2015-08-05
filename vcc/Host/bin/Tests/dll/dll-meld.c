#include "dryad_dll_defs_rev.h"
_(logic \bool mutable_list(DLNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
void dll_meld(DLNode * u, DLNode * v)
  _(requires dll(v))
  _(requires dll_rev(u))
  _(requires \oset_disjoint(dll_reach(v), dll_reach_rev(u)))
  _(ensures dll(v))
  _(ensures dll_rev(u))
  _(ensures \oset_disjoint(dll_reach(v), dll_reach_rev(u)))
  _(ensures u != NULL ==> u->next == v)
  _(ensures v != NULL ==> v->prev == u)
{
  _(assume mutable_list(u))
  _(assume mutable_list(v))
  if (v != NULL) {
    v->prev = u;
  } 

  if (u != NULL) {
    u->next = v;
  }
 
}

