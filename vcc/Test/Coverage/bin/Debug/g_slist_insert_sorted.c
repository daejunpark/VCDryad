#include "sll.h"

Node * g_slist_insert_sorted(Node * list, int data)
	_(requires _dryad_srtl(list))
	_(ensures  _dryad_srtl(\result))
	_(ensures  _dryad_keys(\result) == \intset_union(\old(_dryad_keys(list)), \intset_singleton(data)))
{
	_(assume mutable_list(list))
	Node * tmp_list = list;
	Node * prev_list = NULL;
	Node * new_list = NULL;

	if (list == NULL) {
		new_list = (Node *) malloc(sizeof(Node));
		_(assume new_list != NULL)
		new_list->key = data;
		new_list->next = NULL;
		return new_list;
	}

	while(tmp_list->next != NULL && tmp_list->key < data) 
		_(invariant \subset(_dryad_N(tmp_list), _dryad_N(list)))
		_(invariant \subset(_dryad_N(prev_list), _dryad_N(list)))
		_(invariant \subset(_dryad_lsegN(list, tmp_list), _dryad_N(list)))
		_(invariant \subset(_dryad_lsegN(list, prev_list), _dryad_N(list)))
		_(invariant _dryad_srtl(list))
		_(invariant _dryad_srtl(prev_list))
		_(invariant _dryad_srtl(tmp_list))
		_(invariant \srtlsegStar(list, tmp_list))
		_(invariant \srtlsegStar(list, prev_list))
		_(invariant prev_list == NULL ==> tmp_list == list)
		_(invariant prev_list != NULL ==> prev_list->next == tmp_list)
		_(invariant prev_list != NULL ==> \intset_ge(data, _dryad_lsegk(list, prev_list)))
		_(invariant prev_list != NULL ==> \intset_ge(data, _dryad_lsegk(list, tmp_list)))
		_(invariant prev_list != NULL ==> data >= prev_list->key)
		_(invariant mutable_list(prev_list))
		_(invariant tmp_list != NULL && mutable_list(tmp_list))
	{
		_(assume unfoldMutable(tmp_list))
		prev_list = tmp_list;
		tmp_list = tmp_list->next;
	}

	new_list = (Node *) malloc(sizeof(Node));
	_(assume new_list != NULL)
	new_list->key = data;
	if (tmp_list->next == NULL && data >= tmp_list->key) { 
		tmp_list->next = new_list;
		new_list->next = NULL;
		return list;
	}

	if (prev_list != NULL) {
		new_list->next = NULL;
		prev_list->next = new_list;
		_(ghost LemmaSkipSort(list, prev_list) ;)
		new_list->next = tmp_list;
		return list;
	} else {
		new_list->next = list;
		return new_list;
	}
}	
