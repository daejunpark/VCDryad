#include "dryad_slave_dll.h"

_(dryad)
struct slave_item * alloc_or_die_slave(void)
  _(ensures slave_dll(\result))
  _(ensures \result->next == NULL)
  _(ensures \result->prev == NULL)
{
  struct slave_item * ptr = (struct slave *)malloc(sizeof(*ptr));
  if (!ptr)
    abort();

  ptr->next = NULL;
  ptr->prev = NULL;
  return ptr;
}

