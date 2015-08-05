#include "dryad_sl.h"

_(dryad)
Node * rec_filter(Node * x)
  _(requires sll(x))
  _(ensures sll(\result))
{
  _(assume mutable_list(x))
  _(assume x != NULL ==> \malloc_root(x))

  Node * n1;
  Node * n2;
  int nondet;
  if (x == NULL) { 
    return x;
  } else if (nondet) { 
    n1 = x->next;
    n2 = rec_filter(n1);
    x->next = n2;
    return x;
  } else {
    n1 = x->next;
    free(x);
    n2 = rec_filter(n1);
    return n2;
  }
}
