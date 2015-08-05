#include "sll.h"

Node * g_slist_copy(Node * list)
	_(requires _dryad_sll(list))
	_(ensures \sllStar(list, \result))
	_(ensures _dryad_keys(\result) == _dryad_keys(list)) 

{
	_(assume mutable_list(list))
  _(ghost \objset ALL_REACH = _dryad_N(list) ;)
  _(ghost Node * old_list = \old(list) ;)

	Node * new_list = NULL;
	if (list != NULL) {
		Node * last = NULL;

		new_list = (Node *) malloc(sizeof(Node));
		_(assume new_list != NULL)
    _(ghost ALL_REACH = ALL_REACH \union {new_list} ;)
    
    int list_key = list->key;
		new_list->key = list_key;
		new_list->next = NULL; 

		last = new_list;

		_(assume unfoldMutable(list))
		list = list->next; 

		while(list != NULL)
			_(invariant \sllStar(old_list, new_list))
			_(invariant \sllStar(list, new_list))
			_(invariant \lsegStar(old_list, list)) 
			_(invariant \lsegStar(new_list, last))
			_(invariant \disjoint(_dryad_N(list), _dryad_N(last)))
			_(invariant \disjoint(_dryad_N(old_list), _dryad_N(last))) 
			_(invariant last->next == NULL)
			_(invariant \subset(_dryad_N(old_list), ALL_REACH)) 
			_(invariant \subset(_dryad_N(list), ALL_REACH)) 
			_(invariant \subset(_dryad_N(new_list), ALL_REACH))
			_(invariant \subset(_dryad_N(list), _dryad_N(old_list)))
			_(invariant \subset(_dryad_N(last), _dryad_N(new_list)))
			_(invariant \subset(_dryad_lsegN(old_list, list), _dryad_N(old_list))) 
			_(invariant _dryad_keys(new_list) == _dryad_lsegk(old_list, list))
			//_(invariant _dryad_sll(old_list))
			//_(invariant _dryad_sll(last))
			//_(invariant _dryad_sll(list))
			_(invariant mutable_list(list))
			_(invariant last != NULL && mutable_list(last))
		{
			Node * tail = (Node *)malloc(sizeof(Node));
			_(assume tail != NULL)
      _(assume !(tail \in ALL_REACH))
      _(ghost ALL_REACH = ALL_REACH \union {tail} ;)

      int list_key = list->key;
 			tail->key = list_key;
			tail->next = NULL;

			last->next = tail;
			last = last->next;

      _(assume unfoldMutable(list))
			list = list->next;
		}
	}
	
	return new_list;
}
