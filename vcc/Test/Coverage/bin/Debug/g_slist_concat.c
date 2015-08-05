#include "sll.h"
Node * g_slist_last(Node * list)
  _(requires _dryad_sll(list))
  _(ensures  \unchangedSll(list))
  _(ensures _dryad_sll(\result))
  _(ensures _dryad_keys(list) == \old(_dryad_keys(list)))
  _(ensures list != NULL ==> \result != NULL)
  _(ensures !(\result \in _dryad_lsegN(list, \result)))
  _(ensures \lsegStar(list, \result))
  _(ensures \subset(_dryad_lsegN(list, \result), _dryad_N(list)))
  _(ensures \result != NULL ==> _dryad_keys(\result) == \intset_singleton(\result->key))
;

Node * g_slist_concat(Node * list1, Node * list2)
  _(requires \sllStar(list1, list2))
  _(ensures _dryad_sll(\result))
  _(ensures _dryad_keys(list2) == \old(_dryad_keys(list2)))
  _(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(list1)), _dryad_keys(list2)))
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
