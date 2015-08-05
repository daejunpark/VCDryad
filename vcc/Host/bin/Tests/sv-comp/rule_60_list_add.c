#include "dryad_rule60.h"

_(dryad)
void * list_add(struct list_head * elem, struct list_head * head)
  _(requires elem != NULL)
  _(requires head != NULL)
  _(requires !\oset_in(elem, dllnext_reach(head)))
  _(requires !\oset_in(elem, dllprev_reach(head)))
  _(requires dllnext(head))
  _(requires dllprev(head))
  _(requires !\oset_in(head->next, dllprev_reach(head)))
  _(requires !\oset_in(head->prev, dllnext_reach(head)))
  _(requires \oset_intersect(dllnext_reach(head), dllprev_reach(head)) == \oset_singleton(head))

  _(ensures dllnext(head))
  _(ensures dllprev(head))
  _(ensures dllprev(elem))
  _(ensures dllnext(elem))
  _(ensures head->next == elem)
  _(ensures !\oset_in(head->next, dllprev_reach(head)))
  _(ensures !\oset_in(head->prev, dllnext_reach(head)))
  _(ensures \oset_intersect(dllnext_reach(head), dllprev_reach(head)) == \oset_singleton(head))
  _(ensures !\oset_in(elem->next, dllprev_reach(elem)))
  _(ensures !\oset_in(elem->prev, dllnext_reach(elem)))
  _(ensures \oset_intersect(dllnext_reach(elem), dllprev_reach(elem)) == \oset_singleton(elem))
{

    struct list_head * next = head->next;
    elem->next = NULL;
    elem->prev = NULL;
    elem->inserted = 1;
    head->next = elem;
    elem->prev = head;
    elem->next = next;
    next->prev = elem;
}

