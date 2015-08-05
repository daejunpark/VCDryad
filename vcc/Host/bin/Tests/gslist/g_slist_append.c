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
  _(ensures sll_lseg(list, \result) && \oset_disjoint(sll_lseg_reach(list, \result), sll_reach(\result)))//\lsegStar(list, \result))
  _(ensures \oset_subset(sll_lseg_reach(list, \result), sll_reach(list)))
  _(ensures \result != NULL ==> sll_keys(\result) == \intset_singleton(\result->key))
;

_(dryad)
Node * g_slist_append(Node * list, int data)
  _(requires sll(list))
  _(ensures sll(\result))
  _(ensures sll_keys(\result) == \intset_union(\old(sll_keys(list)), \intset_singleton(data)))
{
  _(assume mutable_list(list))

  Node * new_list = (Node *) malloc(sizeof(Node));
  _(assume new_list != NULL)

  new_list->key = data;
  new_list->next = NULL;
  if (list != NULL) {
    Node * last = g_slist_last(list);
    _(assume mutable_list(last))

    last->next = new_list;

    return list;
  } else {
    return new_list;
  }

}
