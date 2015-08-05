#include "dryad_gslist.h"

_(dryad)
Node * g_slist_prepend (Node * list, int data)
  _(requires sll(list))
  _(ensures  sll(\result))
  _(ensures  sll_keys(\result) == \intset_union(\old(sll_keys(list)), \intset_singleton(data)))
  _(ensures  ! \oset_in(\result, \old(sll_reach(list))))
{
  Node * new_list = (Node *) malloc(sizeof(Node));
  _(assume new_list != NULL)
  new_list->key = data;
  new_list->next = list;    
  return new_list;
}

