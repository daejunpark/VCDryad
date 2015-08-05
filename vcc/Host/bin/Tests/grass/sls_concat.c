#include "dryad_sls.h"

_(dryad)
Node * sls_concat(Node * a, Node * b)
  _(requires srtl(a))
  _(requires srtl(b))
  _(requires b != NULL ==> \intset_le(sll_keys(a), \intset_singleton(b->key)))
  _(requires \oset_disjoint(srtl_reach(a), srtl_reach(b)))
  _(ensures srtl(\result))
{
  _(assume mutable_list(a))
  if (a == NULL) {
    return b;
  }  else {
    Node * curr;
    curr = a;
    while(curr->next != NULL) 
      _(invariant curr != NULL)
      _(invariant srtl(a))
      _(invariant srtl(curr))
      _(invariant srtl_lseg(a, curr))
      _(invariant \oset_disjoint(srtl_lseg_reach(a, curr), srtl_reach(curr)))
      _(invariant mutable_list(curr))
    {
       curr = curr->next;
       _(assume mutable_list(curr))
    }
    curr->next = b;
    return a;
  }
}
