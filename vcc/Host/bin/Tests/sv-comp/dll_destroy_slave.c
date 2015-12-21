#include "dryad_slave_dll.h"

_(logic \bool mutable_slave_dll(struct slave_item * x) = x != NULL ==> \mutable(x) && \writable(x))
_(abstract) void abort_()
    _(ensures \false) 
;

_(dryad)
void dll_destroy_slave(struct slave_item * dll _(out \oset ALL_REACH))
  _(requires slave_dll(dll))
  _(ensures ALL_REACH == \oset_empty())
{
  _(assume mutable_slave_dll(dll))
  _(assume dll != NULL ==> \malloc_root(dll))
  _(ghost ALL_REACH = slave_dll_reach(dll))

  struct slave_item * d = dll;
  while(d != NULL)
    _(invariant slave_dll(d))
    _(invariant mutable_slave_dll(d))
    _(invariant d != NULL ==> \malloc_root(d))
    _(invariant ALL_REACH == slave_dll_reach(d))
  {
    _(assume d != NULL && d->next != NULL ==> (\malloc_root(d->next) == \malloc_root(d)))
    _(assume d != NULL && d->next != NULL ==> (mutable_slave_dll(d->next) == mutable_slave_dll(d)))
    struct slave_item * next = d->next;
    free(d);
    _(ghost ALL_REACH = \oset_diff(ALL_REACH, \oset_singleton(d)))
    d = next;
    _(assume mutable_slave_dll(d))
  }
}
