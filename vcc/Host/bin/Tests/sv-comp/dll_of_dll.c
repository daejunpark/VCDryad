#include "dryad_slave_dll.h"

_(logic \bool mutable_slave_dll(struct slave_item * x) = x != NULL ==> \mutable(x) && \writable(x))
_(abstract) void abort_()
    _(ensures \false) 
;

_(dryad)
struct slave_item * alloc_or_die_slave(void)
  _(ensures slave_dll(\result))
  _(ensures \result != NULL)
  _(ensures \result->next == NULL)
  _(ensures \result->prev == NULL)
{
  struct slave_item * ptr = (struct slave_item *) malloc(sizeof(struct slave_item));
  if (!ptr) {
    abort_();
  }

  ptr->next = NULL;
  ptr->prev = NULL;
  return ptr;
}

_(dryad)
struct slave_item * dll_insert_slave(struct slave_item * x)
  _(requires slave_dll(x))
  _(ensures slave_dll(x))
  _(ensures slave_dll(\result))
{
  struct slave_item * item = (struct slave_item *) malloc(sizeof(struct slave_item));
  if (!item) {
    abort_();
  }
  item->next = NULL;
  item->prev = NULL;

  struct slave_item * next = x;
  item->next = next;
  if (next != NULL) {
    next->prev = item;
  }  
  return item;
}

_(dryad)
struct slave_item * dll_create_slave(int n)
  _(ensures slave_dll(\result))
{
  struct slave_item * dll = NULL;
  dll = dll_insert_slave(dll);
  dll = dll_insert_slave(dll);
  while(n > 0) 
    _(invariant slave_dll(dll))
  {
    dll = dll_insert_slave(dll);
  }
  return dll;
}

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
