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


Node * g_slist_append(Node * list, int data)
  _(requires _dryad_sll(list))
  _(ensures _dryad_sll(\result))
  _(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(list)), \intset_singleton(data)))
{
  _(assume mutable_list(list))
  Node * new_list;
  Node * last;

  _(assert _dryad_sll(list))
  new_list = (Node *) malloc(sizeof(Node));
  _(assume new_list != NULL)

  _(assert _dryad_sll(list))
  new_list->key = data;
  new_list->next = NULL;
  if (list != NULL) {
    last = g_slist_last(list);
    _(assume mutable_list(last))

    last->next = new_list;

    return list;
  } else {
    return new_list;
  }

}
