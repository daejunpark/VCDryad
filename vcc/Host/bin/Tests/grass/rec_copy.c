#include "dryad_sl.h"

_(dryad) 
Node * rec_copy_loop(Node * curr, Node * cp)
  _(requires sll(cp))
  _(requires sll(curr))
  _(requires \oset_disjoint(sll_reach(cp), sll_reach(curr)))
  _(ensures sll(\result))
  _(ensures sll(curr))
  _(ensures \oset_disjoint(sll_reach(\result), sll_reach(curr)))
{
  _(assume mutable_list(curr))
  _(assume mutable_list(cp))
  if (curr == NULL) {
    return cp;
  } else {
    Node * old_cp = cp;
    cp = (Node *) malloc(sizeof(Node));
    _(assume cp != NULL)
    cp->next = old_cp;
    Node * curr_next = curr->next;
    Node * res = rec_copy_loop(curr_next, cp);
    return res;
  }
}

_(dryad)
Node * rec_copy(Node * lst) 
  _(requires sll(lst))
  _(ensures sll(lst))
  _(ensures sll(\result))
  _(ensures \oset_disjoint(sll_reach(lst), sll_reach(\result)))
{
  return rec_copy_loop(lst, NULL);
}
