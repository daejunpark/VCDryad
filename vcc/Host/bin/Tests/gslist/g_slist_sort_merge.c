#include "dryad_gslist.h"

_(dryad)
Node * g_slist_sort_merge(Node * l1, Node * l2)
	_(requires srtl(l1) && srtl(l2) && \oset_disjoint(srtl_reach(l1), srtl_reach(l2)))
	_(ensures srtl(\result))
//	_(ensures sll_keys(\result) == \intset_union(\old(sll_keys(l1)), \old(sll_keys(l2))))
//	_(ensures sll_reach(\result) == \oset_union(\old(sll_reach(l1)), \old(sll_reach(l2))))
{
	_(ghost \intset k1 = sll_keys(l1) ;)
	_(ghost \intset k2 = sll_keys(l2) ;)
	_(ghost \intset init_sll_keys = \intset_union(sll_keys(l1), sll_keys(l2)) ;)
	_(ghost \oset INIT_REACH = \oset_union(sll_reach(l1), sll_reach(l2)) ;)
	
	Node * list, * l;
	_(assume mutable_list(l1) && mutable_list(l2))

	list = (Node *) malloc(sizeof(Node));
	_(assume list != NULL)
	//_(assume !\oset_in(list, INIT_REACH))



	// list head is a (sort of) sentinel node
	// it can be also thought as bottom (in this case -inf)
	list->key = INT_MIN; 
	list->next = NULL; 
	l = list;
    _(assume l1 != NULL ==> INT_MIN <= sll_min_key(l1))
    _(assume l2 != NULL ==> INT_MIN <= sll_min_key(l2))
  _(assume mutable_list(l))
  Node * list_next =list->next;
	while(l1 != NULL && l2 != NULL)
        _(invariant srtl_lseg(list,l))
        _(invariant srtl(l1))
        _(invariant srtl(l2))

        _(invariant \oset_disjoint(srtl_lseg_reach(list,l), srtl_reach(l1)))
        _(invariant \oset_disjoint(srtl_lseg_reach(list,l), srtl_reach(l2)))
        _(invariant \oset_disjoint(srtl_reach(l1), srtl_reach(l2)))

        _(invariant !\oset_in(l, srtl_lseg_reach(list,l)))
        _(invariant !\oset_in(l, srtl_reach(l1)))
        _(invariant !\oset_in(l, srtl_reach(l2)))

        _(invariant list != l ==> sll_lseg_max_key(list,l) <= l->key)
        _(invariant l1 != NULL ==> l->key <= sll_min_key(l1))
        _(invariant l2 != NULL ==> l->key <= sll_min_key(l2))

        _(invariant l != NULL)

      //_(invariant list != l ==>
      //    \intset_union(\old(sll_keys(l1)), \old(sll_keys(l2)))
      //    == \intset_union(sll_lseg_keys(list->next,l),
      //       \intset_union(\intset_singleton(l->key),
      //       \intset_union(sll_keys(l1), sll_keys(l2))))
      //)
      //_(invariant list == l ==>
      //    \intset_union(\old(sll_keys(l1)), \old(sll_keys(l2)))
      //    == \intset_union(sll_keys(l1), sll_keys(l2))
      //)

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
	if (l1 != NULL) {
		l->next = l1;
	} else {
		l->next = l2;
	}
	return list_next;
}
