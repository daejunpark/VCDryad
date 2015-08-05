#include "sll.h"

Node * g_slist_sort_merge(Node * l1, Node * l2)
	_(requires \srtlStar(l1, l2))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(l1)), \old(_dryad_keys(l2))))
	_(ensures _dryad_N(\result) == (\old(_dryad_N(l1)) \union \old(_dryad_N(l2))))
{
	_(ghost \intset k1 = _dryad_keys(l1) ;)
	_(ghost \intset k2 = _dryad_keys(l2) ;)
	_(ghost \intset init_keys = \intset_union(_dryad_keys(l1), _dryad_keys(l2)) ;)
  _(ghost \objset INIT_REACH = _dryad_N(l1) \union _dryad_N(l2) ;)

	Node * list, * l;
	_(assume mutable_list(l1) && mutable_list(l2))

	list = (Node *) malloc(sizeof(Node));
	_(assume list != NULL)


	// list head is a (sort of) sentinel node
	// it can be also thought as bottom (in this case -inf)
	list->key = INT_MIN; 
	list->next = NULL; 
	l = list;
	
	while(l1 != NULL && l2 != NULL)
		_(invariant \intset_le(l->key, _dryad_keys(l1)))
		_(invariant \intset_le(l->key, _dryad_keys(l2)))
		_(invariant \srtlStar(l, l1))
		_(invariant \srtlStar(l, l2))
		_(invariant \srtlStar(l1, l2))
		_(invariant \srtlsegStar(list, l)) 
		_(invariant \disjoint(_dryad_N(l1), _dryad_lsegN(list, l))) 
		_(invariant \disjoint(_dryad_N(l2), _dryad_lsegN(list, l))) 
		_(invariant list->next != NULL ==> \srtlsegStar(list->next, l)) // analyze expr to get lseg, see temp workaround
    _(invariant \uselseg(list->next, l)) //  this is temp workaround 
		_(invariant _dryad_srtl(list))
		_(invariant _dryad_srtl(list->next))
		_(invariant list->next == NULL ==> l == list)
    // this is a workaround for the invariant below
		_(invariant init_keys == \intset_union(_dryad_keys(list->next), \intset_union(_dryad_keys(l1), _dryad_keys(l2)))) 
		//_(invariant \intset_union(k1, k2) == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2)))) // this does not work, see above for a workaround
		_(invariant INIT_REACH == (_dryad_N(list->next) \union _dryad_N(l1) \union _dryad_N(l2)))
    _(invariant list->next != NULL ==> init_keys == _dryad_keys(list->next))
		_(invariant l->next == NULL)
		_(invariant l != NULL)
		_(invariant mutable_list(l))
		_(invariant mutable_list(l1))
		_(invariant mutable_list(l2))
	{
		_(assume unfoldMutable(l))
		if (l1->key <= l2->key)
		{
			l->next = l1;
			_(assume unfoldMutable(l1))
			l1 = l1->next;
		} else {
			l->next = l2;

			_(assume unfoldMutable(l2))
			l2 = l2->next;
		}
		l = l->next;

		l->next = NULL;
	}
  
	if (l1 != NULL) {
		l->next = l1;
		_(ghost LemmaSkipSort(list->next, l))

	} else {
		l->next = l2;
		_(ghost LemmaSkipSort(list->next, l))
	}
  // TODO: why is this needed? UPDATE: not needed if stated as an invariant
  //_(assert init_keys == _dryad_keys(list->next))
	return list->next;
}
