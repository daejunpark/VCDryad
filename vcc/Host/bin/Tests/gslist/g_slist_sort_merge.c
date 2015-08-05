#include "dryad_gslist.h"

_(dryad)
Node * g_slist_sort_merge(Node * l1, Node * l2)
	_(requires srtl(l1) && srtl(l2) && \oset_disjoint(srtl_reach(l1), srtl_reach(l2)))
	_(ensures srtl(\result))
    _(ensures \result != NULL)
	_(ensures sll_keys(\result) == \intset_union(\old(sll_keys(l1)), \old(sll_keys(l2))))
	_(ensures sll_reach(\result) == \oset_union(\old(sll_reach(l1)), \old(sll_reach(l2))))
{
	_(ghost \intset k1 = sll_keys(l1) ;)
	_(ghost \intset k2 = sll_keys(l2) ;)
	_(ghost \intset init_sll_keys = \intset_union(sll_keys(l1), sll_keys(l2)) ;)
	_(ghost \oset INIT_REACH = \oset_union(sll_reach(l1), sll_reach(l2)) ;)
	
	Node * list, * l;
	_(assume mutable_list(l1) && mutable_list(l2))

	//_(assert \false)
	list = (Node *) malloc(sizeof(Node));
	_(assume list != NULL)
	_(assert \false)
	//_(assume !\oset_in(list, INIT_REACH))



	// list head is a (sort of) sentinel node
	// it can be also thought as bottom (in this case -inf)
	list->key = INT_MIN; 
	list->next = NULL; 
	l = list;
  _(assume mutable_list(l))
  Node * list_next =list->next;
	_(assert \false)
	while(l1 != NULL && l2 != NULL)
		_(invariant \intset_le_one1(l->key, sll_keys(l1)))
		_(invariant \intset_le_one1(l->key, sll_keys(l2)))
	    _(invariant srtl(l) && srtl(l1) && \oset_disjoint(srtl_reach(l), srtl_reach(l1)))   // \srtlStar(l, l1))
	    _(invariant srtl(l) && srtl(l2) && \oset_disjoint(srtl_reach(l), srtl_reach(l2))) // \srtlStar(l, l2))
	    _(invariant srtl(l1) && srtl(l2) && \oset_disjoint(srtl_reach(l1), srtl_reach(l2))) // \srtlStar(l1, l2))
		_(invariant srtl_lseg(list, l) && \oset_disjoint(srtl_lseg_reach(list, l), srtl_reach(l)))//\srtlsegStar(list, l)) 
		_(invariant list_next != NULL ==> srtl_lseg(list_next, l) && \oset_disjoint(srtl_lseg_reach(list_next, l), srtl_reach(l)))//\srtlsegStar(list_next, l)) // analyze expr to get lseg, see temp workaround
        _(invariant list_next != NULL ==> (\intset_union(\old(sll_keys(l1)), \old(sll_keys(l2))) == sll_keys(list_next)))
		_(invariant srtl(list))
		_(invariant srtl(list_next))
		_(invariant list_next == NULL ==> l == list)
		_(invariant \intset_union(\old(sll_keys(l1)), \old(sll_keys(l2))) == \intset_union(sll_keys(list_next), \intset_union(sll_keys(l1), sll_keys(l2)))) 
		_(invariant INIT_REACH == \oset_union(sll_reach(list_next), \oset_union(sll_reach(l1), sll_reach(l2))))
		_(invariant \oset_disjoint(sll_reach(l1), sll_lseg_reach(list, l))) 
		_(invariant \oset_disjoint(sll_reach(l2), sll_lseg_reach(list, l))) 
		_(invariant l->next == NULL)
		_(invariant l != NULL)
		_(invariant mutable_list(l))
		_(invariant mutable_list(l1))
		_(invariant mutable_list(l2))
	{
		_(assume unfold_mutable_list(l))
		if (l1->key <= l2->key)
		{
			l->next = l1;
			_(assume unfold_mutable_list(l1))
			l1 = l1->next;
		} else {
			l->next = l2;
			_(assume unfold_mutable_list(l2))
			l2 = l2->next;
		}
		l = l->next;

		l->next = NULL;
	}
	_(assert \false)
	if (l1 != NULL) {
		l->next = l1;
	} else {
		l->next = l2;
	}
	_(assert \false)
	return list_next;
}
