#include "dryad_sl.h"

_(dryad)
Node * rec_insert(Node * lst, Node * elt)
  _(requires sll(lst))
  _(requires elt != NULL)
  _(requires elt->next == NULL)
  _(requires !\oset_in(elt, sll_reach(lst)))
  _(ensures sll(\result))
{
  if (lst == NULL) {
    return elt; 
  } else {
    int nondet;
    if (nondet) {
      elt->next = lst;
      return elt;
    } else {
      Node * n1 = lst->next;
      Node * n2 = rec_insert(n1, elt);
      lst->next = n2;
      return lst;
    }
  }
}
