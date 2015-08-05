#include "dryad_rule60.h"


_(dryad)
struct list_head * list_head_init(void)
  _(ensures \result != NULL)
  _(ensures dllnext(\result))
  _(ensures dllprev(\result))
  _(ensures dllnext_reach(\result) == \oset_singleton(\result))
  _(ensures dllprev_reach(\result) == \oset_singleton(\result))
{
  struct list_head * head = (struct list_head *) malloc(sizeof(*head));
  _(assume head != NULL)
  head->prev = NULL;
  head->next = NULL;
  head->inserted = 1;
  return head;
}

