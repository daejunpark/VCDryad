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
{
  _(assume mutable_list(list))
  _(ghost Node * old_list = \old(list); )
  if (list != NULL) 
  {
    while(list->next != NULL) 
      _(invariant _dryad_sll(list))
      _(invariant _dryad_sll(old_list))
      _(invariant \lsegStar(old_list, list))
      _(invariant list != NULL && mutable_list(list))
      _(invariant \subset(_dryad_N(list), _dryad_N(old_list)))
      _(invariant \subset(_dryad_lsegN(\old(list), list), _dryad_N(old_list)))
      _(invariant _dryad_keys(list) == \intset_union(_dryad_keys(list->next), \intset_singleton(list->key)))
    {
      list = list->next;
      _(assume mutable_list(list))
    }
   
  }
  return list;
}
