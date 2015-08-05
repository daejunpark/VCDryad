#include "dryad_rule60.h"

_(dryad)
void * list_del(struct list_head * entry)
  _(requires entry != NULL)
  _(requires dllnext(entry))
  _(requires dllprev(entry))
  _(requires !\oset_in(entry->next, dllprev_reach(entry)))
  _(requires !\oset_in(entry->prev, dllnext_reach(entry)))
  _(requires \oset_intersect(dllnext_reach(entry), dllprev_reach(entry)) == \oset_singleton(entry))
  
{
  struct list_head * prev = entry->prev;
  struct list_head * next = entry->next;
  entry->inserted = 0;
  if (prev != NULL) {
    prev->next = next;
  }
  if (next != NULL) {
    next->prev = prev;
  }
  entry->next = NULL;
  entry->prev = NULL;
}

