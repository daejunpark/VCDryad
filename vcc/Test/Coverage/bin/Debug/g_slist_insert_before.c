#include "sll.h"

Node * g_slist_insert_before(Node * slist, Node * sibling, int data)
  _(requires _dryad_sll(slist))
  _(requires _dryad_sll(sibling))
  _(requires \lsegStar(slist, sibling))
  _(ensures _dryad_sll(slist))
  _(ensures _dryad_sll(\result))
  _(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(slist)), \intset_singleton(data)))
{
  if (slist == NULL) {
    slist = (Node *) malloc (sizeof (Node));
    _(assume slist != NULL)
    slist->key = data;
    slist->next = NULL;
    return slist;
  }
  _(assume mutable_list(slist))
  Node * node = NULL;
  Node * last = NULL;
  node = slist;

  while(node != NULL && node != sibling) 
    _(invariant _dryad_sll(node))
    _(invariant _dryad_sll(last))
    _(invariant \lsegStar(slist, node))
    _(invariant \lsegStar(slist, last))
    _(invariant \subset(_dryad_N(node), _dryad_N(slist)))
    _(invariant \subset(_dryad_N(last), _dryad_N(slist)))
    _(invariant \subset(_dryad_lsegN(slist, node), _dryad_N(slist)))
    _(invariant \subset(_dryad_lsegN(slist, last), _dryad_N(slist)))
    _(invariant mutable_list(node))
    _(invariant mutable_list(last))
  {
    last = node;
    node = last->next;
    _(assume mutable_list(node))
  }
  if (last == NULL) {
    node = (Node *) malloc (sizeof(Node));
    _(assume node != NULL)
    node->key = data;
    node->next = slist;
    return node;
  } else {
    node = (Node *) malloc (sizeof(Node));
    _(assume node != NULL)
    Node * tmp_last = last->next;
    node->key = data;
    node->next = tmp_last;
    last->next = node;
    return slist;
  }
}
