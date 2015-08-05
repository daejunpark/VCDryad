#include "sll.h"

Node * g_slist_prepend (Node * list, int data)
  _(requires _dryad_sll(list))
  _(ensures  _dryad_sll(\result))
  _(ensures  _dryad_keys(\result) == \intset_union(\old(_dryad_keys(list)), \intset_singleton(data)))
  _(ensures  ! (\result \in \old(_dryad_N(list))))
;
Node * g_slist_append(Node * list, int data)
  _(requires _dryad_sll(list))
  _(ensures _dryad_sll(\result))
  _(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(list)), \intset_singleton(data)))
;

Node * g_slist_insert(Node * list, int data, int pos)
  _(requires _dryad_sll(list))
  _(ensures _dryad_sll(\result))
  _(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(list)), \intset_singleton(data)))
{
  if (pos < 0) {
    return g_slist_append(list, data);
  } 
  if (pos == 0) {
    return g_slist_prepend(list, data);
  }
  _(assume mutable_list(list))    

  Node * prev_list;
  Node * tmp_list;
  Node * new_list;

  new_list = (Node *) malloc(sizeof(Node));
  _(assume new_list != NULL)
  new_list->key = data;

  if (list == NULL) {
    new_list->next = NULL;
    return new_list;
  }

  tmp_list = list;
  prev_list = tmp_list;

  while(pos > 0 && tmp_list != NULL)
    _(invariant prev_list == tmp_list || prev_list->next == tmp_list)
    _(invariant prev_list != tmp_list ==> prev_list->next == tmp_list)
    _(invariant pos >= 0)
    _(invariant _dryad_sll(tmp_list))
    _(invariant _dryad_sll(prev_list))
    _(invariant _dryad_sll(list))
    _(invariant \lsegStar(list, tmp_list))
    _(invariant \lsegStar(list, prev_list))
    _(invariant \subset(_dryad_N(tmp_list), _dryad_N(list)))
    _(invariant \subset(_dryad_N(prev_list), _dryad_N(list)))
    _(invariant !(new_list \in _dryad_lsegN(list, tmp_list)))
    _(invariant !(new_list \in _dryad_lsegN(list, prev_list)))
    _(invariant prev_list != NULL && mutable_list(prev_list))
    _(invariant mutable_list(tmp_list))
  {
    _(assume unfoldMutable(tmp_list))
    pos --;
    prev_list = tmp_list;
    tmp_list = tmp_list->next;
  }

  Node * tmp_prev = prev_list->next;
  new_list->next = tmp_prev;
  prev_list->next = new_list;
  return list;
}
