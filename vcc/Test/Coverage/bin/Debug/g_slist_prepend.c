#include "sll.h"

Node * g_slist_prepend (Node * list, int data)
  _(requires _dryad_sll(list))
  _(ensures  _dryad_sll(\result))
  _(ensures  _dryad_keys(\result) == \intset_union(\old(_dryad_keys(list)), \intset_singleton(data)))
  _(ensures  ! (\result \in \old(_dryad_N(list))))
{
  Node * new_list = (Node *) malloc(sizeof(Node));
  _(assume new_list != NULL)
  new_list->key = data;
  new_list->next = list;    
  return new_list;
}

