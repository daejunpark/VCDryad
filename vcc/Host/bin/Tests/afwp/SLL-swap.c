#include "dryad_SLL.h"

_(dryad)
Node * swap(Node * h _(out Node * old_h)) 
  _(requires sll(h))
  _(ensures  sll(h)) 
  _(ensures sll(\result))
  _(ensures (\result != NULL && \result->next != NULL ==> \result == old_h)
            || \result == h)
{
  if (h != NULL) {
    Node * i = h->next;
    if (i != NULL) {  
      _(ghost old_h = h ;)
      Node * j = h;
      h = h->next;
      Node * t = h->next;
      j->next = t;
      h->next = j;
      return j;
    }
    return h;
  }
  return h;
}
