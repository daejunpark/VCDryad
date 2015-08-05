#include "dryad_sl.h"

_(dryad)
Node * rec_reverse_acc(Node * curr, Node * rev)
  _(requires sll(rev))
  _(requires sll(curr))
  _(requires \oset_disjoint(sll_reach(rev), sll_reach(curr)))
  _(ensures sll(\result))
{
  if (curr == NULL) {
    return rev;
  } else {
    Node * tmp = curr->next;
    curr->next = rev;
    Node * ret = rec_reverse_acc(curr, tmp);
    return ret;
  }
}

_(dryad)
Node * rec_reverse(Node * lst) 
  _(requires sll(lst))
  _(ensures sll(\result))
{
  return rec_reverse_acc(lst, NULL);
}
