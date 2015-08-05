#include "dryad_sl.h"

_(dryad) 
Node * find_last(Node * a)
  _(requires a != NULL)
  _(requires sll(a))
  _(requires sll_lseg(a, NULL))
  _(ensures \result != NULL)
  _(ensures \result->next == NULL)
  _(ensures sll(a))
  _(ensures sll(\result))
  _(ensures sll_lseg(a, \result))
  _(ensures \oset_disjoint(sll_lseg_reach(a, \result), sll_reach(\result)))
{ 
    _(assume mutable_list(a))
    if(a->next != NULL) {
      Node * n2 = find_last(a->next);
      return n2;
    } else {
      return a;
    }
} 

_(dryad)
void rec_concat(Node * a, Node * b)
  _(requires a != NULL)
  _(requires sll(a))
  _(requires sll(b))
  _(requires \oset_disjoint(sll_reach(a), sll_reach(b)))
  _(ensures sll_lseg(a, b))
  _(ensures sll(b))
  _(ensures \oset_disjoint(sll_lseg_reach(a, b), sll_reach(b)))
{
  Node * l = find_last(a);
  l->next = b;
}
