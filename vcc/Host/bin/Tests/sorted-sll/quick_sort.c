#include "dryad_srtl.h"

SNnode * concat_sorted(SNnode * l1, SNnode * l2)
	_(requires srtl(l1) && srtl(l2) && \oset_disjoint(sll_reach(l1), sll_reach(l2)))
	_(requires l2 != NULL ==> \intset_le_one2(sll_keys(l1), l2->key))
	_(ensures srtl(\result))
	_(ensures sll_keys(\result) == \intset_union(\old(sll_keys(l1)), \old(sll_keys(l2))))
;

_(dryad)
SNnode * quick_sort(SNnode * l)
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
	SNnode * curr = l->next;
	_(assume unfold_mutable_list(l))

	int pivot = l->key;
	l->next = NULL;

	SNnode * lpt = NULL;
	SNnode * rpt = NULL;

	SNnode * tmp = curr;

	while(curr != NULL)
		_(invariant \intset_le_one1(pivot, sll_keys(rpt)))
		_(invariant \intset_le_one2(sll_keys(lpt), pivot))
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
	
	SNnode * t2 = quick_sort(l);

	if (lpt == NULL) {
		return t2;
	}
	SNnode * t1 = quick_sort(lpt);
	return concat_sorted(t1, t2);
}
