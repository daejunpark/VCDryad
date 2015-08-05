#include "dryad_gslist.h"

Node * g_slist_sort_merge(Node * l1, Node * l2)
	_(requires srtl(l1) && srtl(l2) && \oset_disjoint(srtl_reach(l1), srtl_reach(l2)))
	_(ensures srtl(\result))
	_(ensures sll_keys(\result) == \intset_union(\old(sll_keys(l1)), \old(sll_keys(l2))))
	_(ensures srtl_reach(\result) == \oset_union(\old(srtl_reach(l1)), \old(srtl_reach(l2))))
	;

_(dryad)
Node * g_slist_sort_real(Node * list)
	_(requires sll(list))
	_(ensures srtl(\result))
	_(ensures sll_keys(\result) == \old(sll_keys(list)))
  _(ensures srtl_reach(\result) == \old(srtl_reach(list)))
{
  _(ghost \oset INIT_REACH = sll_reach(list) ;)
	Node * l1, * l2;
	_(assume mutable_list(list))

	if (list == NULL) {
		return list;
	}
	if (list->next == NULL) {
		return list;
	}
	l1 = list;
	l2 = list->next;
  
	Node * l2_next = l2->next;
	_(assume mutable_list(l2))
	_(assume mutable_list(l2_next))

	while(l2_next != NULL)
    _(invariant sll(list))
		_(invariant sll(l1))
		_(invariant sll_lseg(list, l1) && \oset_disjoint(sll_lseg_reach(list, l1), sll_reach(l1))) //\lsegStar(list, l1))
		_(invariant sll(l2))
		_(invariant sll_lseg(list, l2) && \oset_disjoint(sll_lseg_reach(list, l2), sll_reach(l2))) //\lsegStar(list, l2))
		_(invariant sll_lseg(l1, l2) && \oset_disjoint(sll_lseg_reach(l1, l2), sll_reach(l2))) //\lsegStar(l1, l2))
    _(invariant \oset_subset(sll_reach(l2), sll_reach(l1)))
    _(invariant l2 != NULL)
    _(invariant l2->next == l2_next)
    _(invariant \oset_in(l2, sll_reach(l1)))
	  _(invariant l1 != NULL)
		_(invariant INIT_REACH == \oset_union(sll_lseg_reach(list, l1), \oset_union(sll_lseg_reach(l1, l2), sll_reach(l2))))
		_(invariant \old(sll_keys(list)) == \intset_union(sll_lseg_keys(list, l1), \intset_union(sll_lseg_keys(l1, l2), sll_keys(l2))))
		_(invariant mutable_list(l2))
		_(invariant mutable_list(l2_next))
		_(invariant mutable_list(l1))
	{
		_(assume unfold_mutable_list(l2_next))
    l2_next = l2_next->next;
    l2 = l2_next;
    

		if(l2 == NULL) {
			break;
		}
		_(assume unfold_mutable_list(l1))
		l1 = l1->next;

		_(assume unfold_mutable_list(l2))
		l2_next = l2->next;
	}

  if (l2 != NULL) {
    l2 = l2_next;
  }

  l2 = l1->next;
  l1->next = NULL; 
  
  if (l2 != NULL) {
    Node * t1 = g_slist_sort_real(list);
	  Node * t2 = g_slist_sort_real(l2);
  	return g_slist_sort_merge(t1, t2);
  } else {
    Node * t1 = g_slist_sort_real(list);
    return t1;
  }
}
