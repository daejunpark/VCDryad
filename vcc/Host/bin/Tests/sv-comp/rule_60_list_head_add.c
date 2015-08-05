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

_(dryad)
int main() {
  struct list_head * head = list_head_init();
  struct list_head * dev = malloc(sizeof(*dev));
  
  if (dev != NULL) {
    _(assume dev != head)
    list_add(dev, head);
    list_del(dev);
    // list_add(dev, head); [need list segments to prove this]
  }
}
  
