#include "dryad_sls.h"

_(dryad)
Node * sls_pairwise_sum(Node * x, Node * y)
  _(requires srtl(x))
  _(requires srtl(y))
  _(requires \oset_disjoint(srtl_reach(x), srtl_reach(y)))
  
  _(ensures srtl(x))
  _(ensures srtl(y))
  _(ensures \oset_disjoint(srtl_reach(x), srtl_reach(y)))
  _(ensures srtl(\result))
  _(ensures \oset_disjoint(srtl_reach(\result), srtl_reach(x)))
{
  _(assume mutable_list(x))
  _(assume mutable_list(y))
  _(ghost \oset ALL_REACH = \oset_union(srtl_reach(x), srtl_reach(y)) ;)
  if (x == NULL || y == NULL) {
    return NULL;
  } 
  Node * curr_x = x;
  Node * curr_y = y;
  Node * z = (Node *) malloc(sizeof(Node));
  _(assume z != NULL)
  _(assume !\oset_in(z, ALL_REACH))
  _(ghost ALL_REACH = \oset_union(ALL_REACH, \oset_singleton(z)))
  Node * last_z = z;
  int z_key = _(unchecked) (curr_x->key + curr_y->key);
  z->key = z_key;
  _(assume z->key == curr_x->key + curr_y->key)
  z->next = NULL;
  _(assume mutable_list(curr_x))
  _(assume mutable_list(curr_y))
  _(assume mutable_list(last_z))
  while(curr_x->next != NULL && curr_y->next != NULL)
    _(invariant srtl(x))
    _(invariant srtl(curr_x))
    _(invariant srtl_lseg(x, curr_x))
    _(invariant \oset_disjoint(srtl_reach(curr_x), srtl_lseg_reach(x, curr_x)))

    _(invariant srtl(z))
    _(invariant srtl(last_z))
    _(invariant srtl_lseg(z, last_z))
    _(invariant \oset_disjoint(srtl_reach(last_z), srtl_lseg_reach(z, last_z)))

    _(invariant srtl(y))
    _(invariant srtl(curr_y))
    _(invariant srtl_lseg(y, curr_y))
    _(invariant \oset_disjoint(srtl_reach(curr_y), srtl_lseg_reach(y, curr_y)))

    _(invariant \oset_disjoint(srtl_reach(x), srtl_reach(y)))
    _(invariant \oset_disjoint(srtl_reach(x), srtl_reach(z)))

    _(invariant \oset_subset(srtl_lseg_reach(x, curr_x), ALL_REACH))
    _(invariant \oset_subset(srtl_reach(x), ALL_REACH))
    _(invariant \oset_subset(srtl_lseg_reach(y, curr_y), ALL_REACH))
    _(invariant \oset_subset(srtl_reach(y), ALL_REACH))
    _(invariant \oset_subset(srtl_lseg_reach(z, last_z), ALL_REACH))
    _(invariant \oset_subset(srtl_reach(z), ALL_REACH))

    _(invariant last_z->key == curr_x->key + curr_y->key)
    _(invariant last_z->next == NULL)
    _(invariant mutable_list(curr_x))
    _(invariant mutable_list(curr_y))
    _(invariant mutable_list(last_z))
  {
    Node * tmp = last_z;
    curr_x = curr_x->next;
    curr_y = curr_y->next;
    last_z = (Node *)malloc(sizeof(Node));
    _(assume last_z != NULL)
    _(assume !\oset_in(last_z, ALL_REACH))
    _(ghost ALL_REACH = \oset_union(ALL_REACH, \oset_singleton(last_z)))

    last_z->next = NULL;
    z_key = _(unchecked) (curr_x->key + curr_y->key);
    last_z->key = z_key;
    _(assume last_z->key == curr_x->key + curr_y->key)
    tmp->next = last_z;
    _(assume mutable_list(curr_x))
    _(assume mutable_list(curr_y))
    _(assume mutable_list(last_z))
  }

  return z;
}
