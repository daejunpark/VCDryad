#include "dryad_sls.h"

typedef
struct node_tuple{
  Node * hd;
  Node * tl;
} NodeTuple;

_(dryad)
Node * split(Node * x)
  _(requires sll(x))
  _(ensures \old(sll(x)))
  _(ensures sll(\result))
  _(ensures sll(x))
  _(ensures \oset_disjoint(sll_reach(\result), sll_reach(x)))
{
  _(assume mutable_list(x))
  //Node * y = x;
  Node * z = x;

  Node * curr = x;
  while(curr != NULL)
    _(invariant sll_lseg(x, curr))
    _(invariant \oset_disjoint(sll_lseg_reach(x, curr), sll_reach(curr)))
    _(invariant sll_lseg(x, z))
    _(invariant \oset_disjoint(sll_lseg_reach(x, z), sll_reach(z)))
    _(invariant sll(curr))
    _(invariant sll(z))
    _(invariant sll_lseg(z, curr))
    _(invariant \oset_disjoint(sll_lseg_reach(z, curr), sll_reach(curr)))
    _(invariant mutable_list(curr))
    _(invariant mutable_list(z))
  {
    z = z->next;
    curr = curr->next;
    if (curr != NULL) {
      curr = curr->next;
    }
    _(assume mutable_list(curr))
    _(assume mutable_list(z))
  }
  if (z != NULL) {
    Node * tmp = z;
    z = z->next;
    tmp->next = NULL;
  } 

  return z;
}

