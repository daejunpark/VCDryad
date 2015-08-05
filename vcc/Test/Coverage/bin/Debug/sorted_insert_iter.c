#include "sll.h"

Node * sorted_insert_iter(Node * l, int k)
	_(requires _dryad_srtl(l))
	_(ensures _dryad_srtl(\result))
	_(ensures _dryad_keys(\result) == \intset_union(\old(_dryad_keys(l)), \intset_singleton(k)))
{

	_(assume mutable_list(l))
	if (l == NULL) {
		Node * tl = (Node *) malloc(sizeof(Node));
		_(assume tl != NULL)

		tl->key = k;
		tl->next = NULL;

		return tl;
	} else {
		if (k <= l->key) { // new list is the head

			Node * hd = (Node *) malloc(sizeof(Node));
			_(assume hd != NULL)

			hd->key = k;
			hd->next = l;

			return hd;
			
		} else {
			_(assume unfoldMutable(l))

			Node * prev = l;
      // to show that  _dryad_srtlseg is reflexive one needs one of the follwing
      // a) _(ghost SillyLemma(l))
      // b) _(assume _dryad_unfoldAllLseg(l, l->next))
      // c) _(assert _dryad_srtlseg(l, l))
			Node * next = l->next;
      _(ghost SillyLemma(l) ;)

			while(next != NULL && k > next->key) 
				_(invariant \intset_ge(k, _dryad_lsegk(l, next)))
				_(invariant \subset(_dryad_N(next), _dryad_N(l)))
				_(invariant \subset(_dryad_N(prev), _dryad_N(l)))
				_(invariant \subset(_dryad_lsegN(l, prev), _dryad_N(l)))
				_(invariant \subset(_dryad_lsegN(l, next), _dryad_N(l)))
				_(invariant \disjoint(_dryad_lsegN(l, prev), _dryad_N(next)))
				_(invariant !(prev \in _dryad_N(next))) 
				_(invariant \srtlsegStar(l, prev))
				_(invariant \srtlsegStar(l, next)) 
				_(invariant _dryad_sll(next))         
				_(invariant _dryad_srtl(next))
				_(invariant _dryad_srtl(prev))
				_(invariant prev->key < k)
				_(invariant prev != NULL)
				_(invariant prev->next == next)
				_(invariant mutable_list(next))
				_(invariant mutable_list(prev))
			{
				_(assume unfoldMutable(next))
				prev = next;
				next = next->next;
			}

			Node * curr = (Node *) malloc(sizeof(Node));
			_(assume curr != NULL)

			curr->key = k;
			curr->next = next;
			
			prev->next = curr;
			return l;
		}
	}
}

