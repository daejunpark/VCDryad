#include "dryad_slave_dll.h"

_(logic \bool mutable_slave_dll(struct slave_item * x) = x != NULL ==> \mutable(x) && \writable(x))
_(abstract) void abort_()
    _(ensures \false) 
;

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
