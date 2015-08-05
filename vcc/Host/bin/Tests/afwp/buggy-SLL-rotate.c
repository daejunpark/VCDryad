#include "dryad_SLL_basic.h"

_(dryad)
void buggy_rotate(Node * h, Node * j)
  _(requires sll(h))
  _(requires sll(j))
  _(requires sll_lseg(h, j))
  _(requires \oset_disjoint(sll_lseg_reach(h, j), sll_reach(j)))
  _(ensures sll(h))
  _(ensures sll(j))
  _(ensures sll_lseg(j, h))
  _(requires \oset_disjoint(sll_lseg_reach(j, h), sll_reach(h)))
{
  if (h != NULL && h != j) {
    Node * k = h->next;
    //h->next = NULL;
    j->next = h;
    j = h;
    h = k;
    
  }
}
