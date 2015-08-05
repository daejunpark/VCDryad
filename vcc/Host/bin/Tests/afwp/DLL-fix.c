#include "dryad_DLL.h"
#include "dryad_SLL.h"

_(dryad)
DLNode * polarize(Node * h) 
  _(requires sll(h))
  _(ensures dll(\result))
{
  _(assume mutable_list(h))
  _(ghost \oset ALL_REACH = sll_reach(h))
  Node * i = h;
  DLNode * j = NULL;
  while(i != NULL) 
      _(invariant sll(i))
      _(invariant dll(j))
      _(invariant \oset_disjoint(sll_reach(i), dll_reach(j)))
      _(invariant \oset_subset(sll_reach(i), ALL_REACH))
      _(invariant \oset_subset(dll_reach(j), ALL_REACH))
      _(invariant mutable_list(i))
  { 
    DLNode * k = j;
    j = (DLNode *) malloc(sizeof(DLNode));
    _(assume k != NULL)
    _(assume !\oset_in(k, ALL_REACH))
    _(ghost ALL_REACH = \oset_union(ALL_REACH, \oset_singleton(k)))
    j->next = k;
    k->prev = j;
    i = i->next;
    _(assume mutable_list(i))
  }
  return j;
}
