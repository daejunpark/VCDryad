#include "sll.h"
Node * concat_sorted(Node * l1, Node * l2)
	_(requires _dryad_srtl(l1) && _dryad_srtl(l2) && \disjoint(_dryad_N(l1), _dryad_N(l2)))
	_(requires l2 != NULL ==> \intset_ge(l2->key, _dryad_keys(l1)))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_N(\result) == (\old(_dryad_N(l1)) \union \old(_dryad_N(l2))))
	_(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(l1)), \old(_dryad_keys(l2))))
;

Node * quick_sort(Node * l)
	_(requires _dryad_sll(l))
	_(ensures _dryad_N(\result) == \old(_dryad_N(l)))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_keys(\result) == \old(_dryad_keys(l)))
{

  _(ghost \objset ALL_REACH = _dryad_N(l) ;)
  _(ghost \intset old_keys = _dryad_keys(l) ;)
	if (l == NULL) {
		return l;
	} 

	_(assume mutable_list(l))
	Node * curr = l->next;
	_(assume unfoldMutable(l))

	int pivot = l->key;
	l->next = NULL;

	Node * lpt = NULL;
	Node * rpt = NULL;

	Node * tmp = curr;

	while(curr != NULL)
		_(invariant \intset_le(pivot, _dryad_keys(rpt)))
		_(invariant \intset_ge(pivot, _dryad_keys(lpt)))
		_(invariant _dryad_sll(tmp) && _dryad_sll(curr))
		_(invariant _dryad_sll(lpt) && _dryad_sll(rpt))
		_(invariant \disjoint(_dryad_N(lpt), _dryad_N(rpt)))
		_(invariant \disjoint(_dryad_N(rpt), _dryad_N(curr)))
		_(invariant \disjoint(_dryad_N(lpt), _dryad_N(curr)))
		_(invariant !(l \in _dryad_N(curr))) 
		_(invariant !(l \in _dryad_N(rpt)))
		_(invariant !(l \in _dryad_N(lpt)))
		_(invariant ALL_REACH == (_dryad_N(lpt) \union _dryad_N(rpt) \union _dryad_N(curr) \union {l}))
		_(invariant curr == tmp)
		_(invariant old_keys == \intset_union(_dryad_keys(lpt), \intset_union(_dryad_keys(rpt), \intset_union(_dryad_keys(curr), \intset_singleton(pivot)))))
		_(invariant mutable_list(curr))
	{
		_(assume unfoldMutable(curr))
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
