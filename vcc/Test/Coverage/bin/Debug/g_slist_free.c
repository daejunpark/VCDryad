#include "sll.h"

void g_slist_free(Node * l _(out \objset ALL_REACH))
  _(requires _dryad_sll(l))
  _(ensures ALL_REACH == {})
{
  _(assume mutable_list(l))
  _(assume l != NULL ==> \malloc_root(l))
  _(ghost ALL_REACH = _dryad_N(l))
  
  Node * x = l;
  while(x != NULL)
    _(invariant _dryad_sll(x))
    _(invariant mutable_list(x))
    _(invariant x != NULL ==> \malloc_root(x))
    _(invariant ALL_REACH == _dryad_N(x))
  {
    _(assume unfoldMutable(x))
    _(assume x != NULL && x->next != NULL ==> (\malloc_root(x->next) == \malloc_root(x)))
    Node * next = x->next;
    free(x);
    _(ghost ALL_REACH = ALL_REACH \diff {x} ;)
    x = next;
  }
  
}
