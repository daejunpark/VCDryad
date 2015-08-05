#include "dryad_gslist.h"

Node * g_slist_last(Node * list)
  _(requires sll(list))
  _(ensures  sll(list) == \old(sll(list))
             && sll_reach(list) == \old(sll_reach(list)) 
             && sll_keys(list) == \old(sll_keys(list)))
  _(ensures sll(\result))
  _(ensures sll_keys(list) == \old(sll_keys(list)))
  _(ensures list != NULL ==> \result != NULL)
  _(ensures !\oset_in(\result, sll_lseg_reach(list, \result)))
  _(ensures sll_lseg(list, \result) && \oset_disjoint(sll_lseg_reach(list, \result), sll_reach(\result)))
  _(ensures \oset_subset(sll_lseg_reach(list, \result), sll_reach(list)))
  _(ensures \result != NULL ==> sll_keys(\result) == \intset_singleton(\result->key))
;
_(dryad)
Node * g_slist_concat(Node * list1, Node * list2)
  _(requires sll(list1) && sll(list2) && \oset_disjoint(sll_reach(list1), sll_reach(list2)))
  _(ensures sll(\result))
  _(ensures sll_keys(list2) == \old(sll_keys(list2)))
  _(ensures sll_keys(\result) == \intset_union(\old(sll_keys(list1)), sll_keys(list2)))
{
  if (list2 != NULL) {
    if (list1 != NULL) {
      Node * last = g_slist_last(list1);
      _(assume mutable_list(last))
      last->next = list2;
    } else {
      list1 = list2;
    }
  }
  return list1;
}
