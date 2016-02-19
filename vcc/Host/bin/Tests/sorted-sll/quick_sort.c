#include "dryad_srtl.h"

Node * concat_sorted(Node * l1, Node * l2)
	_(requires srtl(l1) && srtl(l2) && \oset_disjoint(sll_reach(l1), sll_reach(l2)))
	_(requires l1 != NULL && l2 != NULL ==> sll_max_key(l1) <= sll_min_key(l2))
	_(ensures srtl(\result))
	_(ensures sll_keys(\result) == \intset_union(\old(sll_keys(l1)), \old(sll_keys(l2))))
;

_(dryad)
Node * quick_sort(Node * l)
	_(requires sll(l))
	_(ensures srtl(\result))
	_(ensures sll_keys(\result) == \old(sll_keys(l)))
{

  _(ghost \oset ALL_REACH = sll_reach(l) ;)
  _(ghost \intset old_sll_keys = sll_keys(l) ;)
	if (l == NULL) {
		return l;
	} 

	_(assume mutable_list(l))
	Node * curr = l->next;
	_(assume unfold_mutable_list(l))

	int pivot = l->key;
	l->next = NULL;

	Node * lpt = NULL;
	Node * rpt = NULL;

	Node * tmp = curr;

	while(curr != NULL)
		_(invariant rpt != NULL ==> pivot <= sll_min_key(rpt))
		_(invariant lpt != NULL ==> sll_max_key(lpt) <= pivot)
		_(invariant sll(tmp) && sll(curr))
		_(invariant sll(lpt) && sll(rpt))
		_(invariant \oset_disjoint(sll_reach(lpt), sll_reach(rpt)))
		_(invariant \oset_disjoint(sll_reach(rpt), sll_reach(curr)))
		_(invariant \oset_disjoint(sll_reach(lpt), sll_reach(curr)))
		_(invariant !\oset_in(l, sll_reach(curr))) 
		_(invariant !\oset_in(l, sll_reach(rpt)))
		_(invariant !\oset_in(l, sll_reach(lpt)))
		_(invariant ALL_REACH == \oset_union(sll_reach(lpt),\oset_union(sll_reach(rpt), \oset_union(sll_reach(curr), \oset_singleton(l)))))

		_(invariant curr == tmp)
		_(invariant old_sll_keys == \intset_union(sll_keys(lpt), \intset_union(sll_keys(rpt), \intset_union(sll_keys(curr), \intset_singleton(pivot)))))
		_(invariant mutable_list(curr))
	{
		_(assume unfold_mutable_list(curr))
		tmp = curr->next;
		if (curr->key <= pivot) {
			curr->next = lpt;
			lpt = curr;
		} else {		
			curr->next = rpt;
			rpt = curr;
		}

		curr = tmp;
	}

	l->next = rpt;
	
	Node * t2 = quick_sort(l);

	if (lpt == NULL) {
		return t2;
	}
	Node * t1 = quick_sort(lpt);
	return concat_sorted(t1, t2);
}
