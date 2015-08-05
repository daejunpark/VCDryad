#include "dryad_sls.h"

_(dryad)
Node * insertion_sort(Node * lst)
  _(requires sll(lst))
  _(ensures  srtl(lst))
{
  _(assume mutable_list(lst))
  Node * prv = NULL;
  Node * srt = lst;
  while(srt != NULL)
    _(invariant sll(lst))
    _(invariant sll(srt))
    _(invariant sll_lseg(lst, srt))
    _(invariant \oset_disjoint(sll_lseg_reach(lst, srt), sll_reach(srt)))
    _(invariant \oset_subset(sll_lseg_reach(lst, srt), sll_reach(lst)))
    _(invariant \oset_subset(sll_reach(srt), sll_reach(lst)))
    _(invariant srtl_lseg(lst, srt))
    _(invariant \oset_disjoint(srtl_lseg_reach(lst, srt), sll_reach(srt)))
    //_(invariant prv != NULL ==> prv == lst)
    _(invariant prv != NULL ==> \intset_le(\intset_singleton(prv->key), sll_keys(srt)))
    //_(invariant prv != NULL ==> \intset_le(\intset_singleton(prv->key), sll_lseg_keys(lst, srt)))
    _(invariant mutable_list(srt))
  {
    Node * curr = srt->next;
    _(assume mutable_list(curr))
    Node * min = srt;
    while(curr != NULL) 
      _(invariant min != NULL)
      _(invariant sll(lst))
      _(invariant sll(srt))
      _(invariant sll_lseg(lst, srt))
      _(invariant srtl_lseg(lst, srt))
      _(invariant \oset_disjoint(srtl_lseg_reach(lst, srt), sll_reach(srt)))
      _(invariant \oset_disjoint(sll_lseg_reach(lst, srt), sll_reach(srt)))
      _(invariant \oset_subset(sll_lseg_reach(lst, srt), sll_reach(lst)))
      _(invariant \oset_subset(sll_reach(srt), sll_reach(lst)))

      _(invariant sll(min))
      _(invariant sll_lseg(srt, min))
      _(invariant \oset_disjoint(sll_lseg_reach(srt, min), sll_reach(min)))
      _(invariant \oset_subset(sll_lseg_reach(srt, min), sll_reach(srt)))
      _(invariant \oset_subset(sll_reach(min), sll_reach(srt)))

      _(invariant sll(curr))
      _(invariant sll_lseg(srt, curr))
      _(invariant \oset_disjoint(sll_lseg_reach(srt, curr), sll_reach(curr)))
      _(invariant \oset_subset(sll_lseg_reach(srt, curr), sll_reach(srt)))
      _(invariant \oset_subset(sll_reach(curr), sll_reach(srt)))

      _(invariant sll_lseg(min, curr))
      _(invariant \oset_disjoint(sll_lseg_reach(min, curr), sll_reach(curr)))
      _(invariant \oset_subset(sll_lseg_reach(min, curr), sll_reach(min)))
      _(invariant \oset_subset(sll_reach(curr), sll_reach(min)))

      _(invariant prv != NULL ==> \intset_le(\intset_singleton(prv->key), sll_keys(curr)))
      _(invariant prv != NULL ==> prv->key <= min->key;)
      //_(invariant \intset_le(\intset_singleton(min->key), sll_lseg_keys(srt, min)))
      _(invariant \intset_le(\intset_singleton(min->key), sll_lseg_keys(min, curr)))
      _(invariant mutable_list(curr))
    {
      if (curr->key < min->key) {
        min = curr;
      }
      curr = curr->next;
      _(assume mutable_list(curr))
    }
    int tmp = min->key;
    int srt_key = srt->key;
    _(ghost \state s0 = \now())
    min->key = srt_key;
    _(ghost \state s1 = \now())
    prv = srt;
    _(ghost \state s2 = \now())
    srt = srt->next;
    _(ghost \state s3 = \now())
    _(assume mutable_list(srt))
  }
}
