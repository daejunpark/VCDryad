#include <vcc.h>

#include "dryad_list_defs.h"

typedef
struct node {
	int key;
	struct node * next;
} Node;
// TODO: move this to dryad_list_defs?
// ------------------------------------------------
_(logic \bool \lsegStar(\object b,  \object  e) = {:split} lseg(b, e) && \disjoint(lsegN(b, e), N(e)) ;)
_(logic \bool \srtlsegStar(\object b,  \object  e) = {:split} srtlseg(b, e) && \disjoint(lsegN(b, e), N(e)) ;)

_(logic \bool mutable_list(Node * x) =
	x != NULL ==> \mutable(x) && \writable(x))

_(logic \bool unfoldMutable(Node * x) =
	((x != NULL && x->next != NULL)
	==> (\mutable(x) == \mutable(x->next) &&
	     \writable(x) == \writable(x->next)) ) )
// ------------------------------------------------

_(def void LemmaSrtlImplSll(Node * x)
	_(reads \universe())
	_(requires srtl(x))
	_(ensures  srtl(x) && sll(x))
	_(decreases llen(x))
	{ 
		if (x != NULL) {
			_(assume unfoldAllSort(x))
			LemmaSrtlImplSll(x->next);
		}
	}
;)

_(def void LemmaSkip(Node * b, Node * e)
	_(requires srtl(b) && srtl(e) && srtlseg(b, e))
	_(ensures N(b) == lsegN(b, e) \union N(e))
	_(ensures llen(b) == (lseglen(b, e) + llen(e)))
	_(decreases llen(b))
{
	if (b == e) {
		return;
	} else {
		_(assume unfoldAllSort(b))
		_(assume unfoldAllSrtlseg(b, e))
		LemmaSkip(b->next, e);
	}
} ;)



Node * insert(Node *x, int k)
	_(requires srtl(x))
	_(ensures srtl(\result))
	_(ensures sll(\result))
	_(ensures  keys(\result) == \intset_union(\old(keys(x)), \intset_singleton(k)))
{
	_(ghost \objset G0 = N(x) ;)
	_(assume x != NULL ==> \mutable(x) && \writable(x))

	if (x == NULL) {
		Node * tail = (Node *) malloc(sizeof(Node));
		_(assume tail != NULL)
		_(ghost \objset G1 = G0 \union {tail};)

		tail->key = k;
		tail->next = NULL;
		_(assume unfoldAllSort(tail))

		_(assert G1 == N(tail))
		return tail;
	} 
	else if (k > x->key) {
		// locs: x
		// derefs: x
		_(assume unfoldAllSort(x))
		_(ghost \state S1 = \now())

		// locs: x, tmp
		// derefs: x
		Node * tmp = insert(x->next, k);
		_(assume unfoldAllSort(x))
		_(ghost \state S2 = \now())
		_(assume \disjoint(N(tmp), (G0 \diff \at(S1, N(x->next)))))
		_(ghost \objset G1 = (G0 \diff \at(S1, N(x->next)) \union \at(S2, N(tmp))) ;)
		_(assert \intset_le(x->key, keys(tmp)))

		x->next = tmp;
		_(assume unfoldAllSort(x))
		_(ghost \state S3 = \now();)
		_(assume maintainsAcrossSort(x, tmp, S2, S3))
		_(assert srtl(x))

		_(assert G1 == N(x))
		return x;
	} 
	else {
		_(assume unfoldAllSort(x))
		_(ghost \state S1 = \now();)

		Node * head = (Node *) malloc(sizeof(Node));
		_(assume head != NULL)
		_(assume !(head \in G0) ;)

		head->key = k;
		head->next = x;
		//_(assume unfoldAllSort(x))
		_(assume unfoldAllSort(head))
		_(ghost \state S2 = \now();)
		_(assume maintainsAcrossSort(head, x, S1, S2))
		//_(assert srtl(x))
		//_(assert srtl(head))
		_(ghost \objset G1 = G0 \union {head} ;)

		_(ghost LemmaSrtlImplSll(head) ;)
		_(assert G1 == N(head))
		return head;
	}
}


Node * insertion_sort_copy(Node * l)
	_(requires sll(l))
	_(ensures srtl(\result))
	_(ensures keys(\result) == \old(keys(l)))
{
	_(ghost \objset G0 = N(l) ;)
	_(assume mutable_list(l))
	if (l == NULL) {
		return l;
		_(assert srtl(l))
	} else {
		_(assume unfoldAll(l))
		_(ghost \state S1 = \now())
		Node * tl = insertion_sort_copy(l->next);
		_(ghost \state S2 = \now())
		_(assume \disjoint(N(tl), (G0 \diff \at(S1, N(l->next)))))
		_(assume unfoldAllSort(l))

		Node * nl = insert(tl, l->key);
		_(ghost \state S3 = \now())
		_(assume \disjoint(\at(S3, N(nl)), (G0 \diff \at(S1, N(tl)))))
		//free(tl); // complicates verification, client should decide
		return nl;
	}
}

Node * delete_all(Node * x, int k)
	_(requires srtl(x))
	_(ensures  srtl(\result))
	_(ensures  \intset_in(k, \old(keys(x))) ==> (keys(\result) == \intset_diff(\old(keys(x)), \intset_singleton(k))))
	_(ensures !\intset_in(k, \old(keys(x))) ==> (keys(\result) == \old(keys(x))))
{
	_(ghost \objset G0 = N(x))
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	_(assume x != NULL ==> \malloc_root(x))
		
	if (x == NULL) {
		//_(assert !(\intset_in(k, keys(x))))
		return x;
	} else if (x->key == k) {
		_(assume unfoldAllSort(x))
		_(ghost \state S1 = \now() ;)
		//_(assert (\intset_in(k, keys(x))))
		
		Node * tmp = delete_all(x->next, k);
		_(assume unfoldAllSort(x))
		_(ghost \state S2 = \now() ;)
		_(assume \disjoint(\at(S2, N(tmp)), (G0 \diff \at(S1, N(x->next)))))
		_(ghost \objset G1 = (G0 \diff \at(S1, N(x->next)) \union \at(S2, N(tmp))) ;)

		free(x);
		//_(ghost G1 = G1 \diff {x} ;)
		//_(assert (!\intset_in(k, keys(tmp))))

		_(ghost \state S3 = \now() ;)
		_(assume maintainsAcrossSort(x, tmp, S2, S3))

		//_(assert G1 == N(tmp))
		return tmp;
	} else {
		_(assume unfoldAllSort(x))
		_(ghost \state S1 = \now() ;)

		 Node * tmp = delete_all(x->next, k);
		_(assume unfoldAllSort(x))
		_(ghost \state S2 = \now() ;)
		_(assume \disjoint(\at(S2, N(tmp)), (G0 \diff \at(S1, N(x->next)))))
		_(ghost \objset G1 = (G0 \diff \at(S1, N(x->next)) \union \at(S2, N(tmp))) ;)

		x->next = tmp;
		_(assume unfoldAllSort(x))
		_(ghost \state S3 = \now())
		_(assume maintainsAcrossSort(x, tmp, S2, S3))

		_(assert G1 == N(x))
		return x;
	}
}

Node * reverse(Node * l)
	_(requires srtl(l))
	_(ensures rsrtl(\result))
	_(ensures keys(\result) == \old(keys(l)))
{
	_(assume mutable_list(l))
	Node * r = NULL;

	while(l != NULL)
		_(invariant srtl(l))
		_(invariant rsrtl(r))
		_(invariant \disjoint(N(l), N(r)))
		//_(invariant l != NULL && r != NULL ==> l->key >= r->key)
		_(invariant l != NULL ==> \intset_ge(l->key, keys(r)))
		_(invariant \old(keys(l)) == \intset_union(keys(l), keys(r)))
		_(invariant mutable_list(l))
	{
		_(assume unfoldMutable(l))
		//_(assume unfoldAllSort(l))
		_(ghost \state S1 = \now())
		Node * t = l->next;
		_(assume unfoldAllSort(l))
		//_(assert t != NULL ==> t->key >= l->key)
		_(ghost \state S2 = \now())
		
		//_(assert r != NULL ==> r == l)
		//_(assert rsrtl(r))
		l->next = r;
		_(assert l != NULL)
		//_(assert r != NULL)
		_(ghost \state S3 = \now())
		_(assume maintainsAcrossSort(l, t, S2, S3))
		_(assume maintainsAcrossSortRev(l, r, S2, S3))
		//_(assert rsrtl(r))
		_(assume unfoldAllSortRev(l))
		//_(assert rsrtl(l->next))
		//_(assert !(l \in N(r)))
		//_(assert \intset_gt(l->key, keys(r)))
		//_(assert rsrtl(l))
		r = l;
		l = t;
	}
	return r;
}


int find(Node * l, int k)
	_(requires srtl(l))
	_(ensures  srtl(l))
	_(ensures  \intset_in(k, keys(l)) <==> \result == 0)
	_(ensures !\intset_in(k, keys(l)) <==> \result == -1)
{
	_(assume mutable_list(l))
	if (l == NULL) {
		return -1;
	} else if (l->key == k) {
		return 0;
	} else { // l != NULL && l->key != k
		_(assume unfoldAllSort(l))
		_(ghost \state S0 = \now() ;)

		int res = find(l->next, k);
		_(assume unfoldAllSort(l))
		_(ghost \state S1 = \now() ;)
		_(assume maintainsAcross(l, l->next, S0, S1))		
		return res;

	}
}


Node * merge_sort_copy(Node * l1, Node * l2)
	_(requires srtl(l1))
	_(requires srtl(l2))
	_(ensures srtl(\result)) // (srtl-post)
	_(ensures keys(\result) == \intset_union(\old(keys(l1)), \old(keys(l2))))
{
	_(ghost \objset G0 = N(l1) \union N(l2) ;)
	_(assume mutable_list(l1))
	_(assume mutable_list(l2))

	if (l1 == NULL) {
		return l2;
	} else if (l2 == NULL) {
		_(assert l1 != NULL)
		return l1;
	} else {
		_(assert l1 != NULL && l2 != NULL)
		if (l1->key <= l2->key) {
			_(assume unfoldAllSort(l1))
			_(assume unfoldAllSort(l2)) // (unfold-all-sort-l2) shows (intset-le-l1-key-l2-keys)
			_(ghost \state S1 = \now() )
			_(assert \intset_le(l1->key, keys(l2))) // (intset-le-l1-key-l2-keys) shows (intset-le-l1-key-tl-keys)

			Node * tl = merge_sort_copy(l1->next, l2);
			_(ghost \state S2 = \now() )
			_(assume \disjoint(N(tl), (G0 \diff (\at(S1, N(l1->next)) \union \at(S1, N(l2))) )))
			_(ghost \objset G1 = (N(tl) \union (G0 \diff (\at(S1, N(l1->next)) \union \at(S1, N(l2))))) )

			_(assert \intset_le(l1->key, keys(tl))) // (intset-le-l1-key-tl-keys) shows (srtl-nl)
			_(assert srtl(tl))
			Node * nl = (Node *) malloc(sizeof(Node));
			_(assume nl != NULL)
			_(assume ! (nl \in G1))

			nl->key  = l1->key;
			nl->next = tl;
			_(assume unfoldAllSort(nl))
			_(ghost \state S3 = \now() )
			_(assume maintainsAcrossSort(nl, tl, S2, S3))
			_(assert srtl(tl))
			_(assert srtl(nl)) // (srtl-nl) shows (srtl-post)

			return nl;	
		} else {
			_(assume unfoldAllSort(l1))
			_(assume unfoldAllSort(l2))
			_(assert !(l1->key <= l2->key))
			_(ghost \state S1 = \now())

			Node * tl = merge_sort_copy(l1, l2->next);
			_(ghost \state S2 = \now())
			_(assume \disjoint(N(tl), (G0 \diff (\at(S1, N(l1)) \union \at(S1, N(l2->next))))))
			_(ghost \objset G1 = (N(tl) \union (G0 \diff (\at(S1, N(l1)) \union \at(S1, N(l2->next))))) )

			Node * nl = (Node *) malloc(sizeof(Node));
			_(assume nl != NULL)
			_(assume ! (nl \in G1))

			nl->key = l2->key;
			nl->next = tl;
			_(assume unfoldAllSort(nl))
			_(ghost \state S3 = \now())
			_(assume maintainsAcrossSort(nl, tl, S2, S3))

			return nl;

		}
	}
}

Node * insert_iter(Node * l, int k)
	_(requires srtl(l))
	_(ensures srtl(\result))
	_(ensures keys(\result) == \intset_union(\old(keys(l)), \intset_singleton(k)))
{
	_(assume mutable_list(l))
	_(ghost \objset G0 = N(l) ;)

	if (l == NULL) {
		Node * tl = (Node *) malloc(sizeof(Node));
		_(assume tl != NULL)
		_(assume !(tl \in G0))

		tl->key = k;
		tl->next = NULL;
		_(assume unfoldAllSort(tl))

		_(assert srtl(tl))
		return tl;
	} else {
		if (k <= l->key) { // new list is the head
			_(assume unfoldAllSort(l))
			_(assert \intset_le(k, keys(l)))
			_(assert srtl(l))
			_(ghost \state S1 = \now())

			Node * hd = (Node *) malloc(sizeof(Node));
			_(assume hd != NULL)
			_(assume !(hd \in G0))			

			hd->key = k;
			hd->next = l;
			_(assume unfoldAllSort(hd))
			_(ghost \state S2 = \now())
			_(assume maintainsAcrossSort(hd, l, S1, S2))
			_(assert srtl(l))

			_(assert srtl(hd))
			return hd;
			
		} else {
			_(assume unfoldMutable(l))
			_(assume unfoldAllSort(l))
			_(assert srtl(l))

			_(ghost \state S1 = \now() )
			_(assert k > l->key)
//			_(assert !\intset_in(k, keys(l)) && \intset_ge(k, keys(l)))
			_(ghost \state S2 = \now())

			Node * prev = l;
			//_(assert \srtlsegStar(l, l))
			//_(assert \srtlsegStar(l, prev))
			Node * next = l->next;
//			_(assume unfoldLseg(l, next))
			_(ghost \state S3 = \now())
			_(ghost LemmaSrtlImplSll(l))
			_(assert \srtlsegStar(l, next))

			while(next != NULL && k > next->key) 
				_(invariant \intset_ge(k, lsegk(l, next)))
				_(invariant \subset(N(next), G0)) // shows (srtl-next)
				_(invariant \subset(N(prev), G0))
				_(invariant \subset(lsegN(l, prev), G0))
				_(invariant \subset(lsegN(l, next), G0))
				_(invariant \disjoint(lsegN(l, prev), N(next)))
				_(invariant !(prev \in N(next))) // shows (srtl-curr-end)
				_(invariant \srtlsegStar(l, prev))
				_(invariant \srtlsegStar(l, next)) // (lseg-star-l-next) follows from (sll-next)
				_(invariant sll(next))          // (sll-next) shows (lseg-star-l-next)
				_(invariant srtl(next))
				_(invariant srtl(prev))
				_(invariant prev->key < k) // shows (srtl-prev-end)
				_(invariant prev != NULL)
				_(invariant prev->next == next)
				_(invariant mutable_list(next))
				_(invariant mutable_list(prev))
			{
				_(assume unfoldMutable(next))
				_(assume unfoldAllSort(next))
				prev = next;
				next = next->next;
			}
			_(assert srtl(l))
			_(assert srtl(next) && \srtlsegStar(l, next))
			_(assert srtl(prev) && \srtlsegStar(l, prev))
			_(assert next == NULL || (next != NULL && k <= next->key))
			_(assert \intset_ge(k, lsegk(l, next))) // follows from the corresponding loop invariant
			_(assert !(prev \in N(next)))

			// (*)
			//_(assume unfoldAllSort(next)) // !!! (unfold-all-sort-next) shows (intset-le-k-keys-next)
			//_(assert \intset_le(k, keys(next))) // (intset-le-k-keys-next) follows from (unfold-all-sort-next) [unexpected unrolling]

			_(ghost \state S4 = \now())

			Node * curr = (Node *) malloc(sizeof(Node));
			_(assume curr != NULL)
			_(assume !(curr \in G0))

			curr->key = k;
			curr->next = next;
			_(assume unfoldAllSort(curr))
			_(assume unfoldAllSort(next)) // interchangable with (*) [see above], shows (srtl-curr)
			_(ghost \state S5 = \now())
			_(assume maintainsAcrossSort(curr, next, S4, S5))
			_(assume maintainsAcrossSort(curr, prev, S4, S5))
			_(assume maintainsAcrossSort(curr, l, S4, S5))
			_(assume maintainsAcrossSrtlseg(curr, l, prev, S4, S5))
			_(assert srtl(l))
			_(assert srtl(next))
			_(assert srtl(curr)) // follows from (unfold-all-sort-next)
			_(assert srtl(prev))
			_(assert !(prev \in N(curr)))
			//_(assert \intset_le(prev->key, keys(next)))
			//_(assert \intset_le(prev->key, k)
			_(assert prev->key <= k)
			_(assert \intset_le(prev->key, keys(curr)))
			_(assert \disjoint(N(next), lsegN(l, prev)))
			_(assert !(curr \in lsegN(l, prev)))
			_(assert \disjoint(N(curr), lsegN(l, prev)))
			_(assert \srtlsegStar(l, prev))

			
			prev->next = curr;
			_(assume unfoldAllSort(prev))
			_(ghost \state S6 = \now())
			_(assume maintainsAcrossSort(prev, curr, S5, S6))
			_(assume maintainsAcrossSrtlseg(curr, l, prev, S5, S6))
			_(assert srtl(curr)) // (srtl-curr-end)
			_(assert srtl(prev)) // (srtl-prev-end)
			_(assert \srtlsegStar(l, prev))
//			_(assert sll(l))
			_(assert srtl(l))
			return l;
		}
	}
}

Node * find_last(Node * l)
	_(requires srtl(l))
	_(ensures srtl(l))
	_(ensures \srtlsegStar(l, \result)) 
	_(ensures  srtl(\result))
	_(ensures \result == NULL || \result->next == NULL)
	_(ensures \subset(N(\result), N(l)))
	_(ensures \subset(lsegN(l, \result), N(l))) // (find-last-post-subset-lseg-l-res-l) shows (disjoint
	_(ensures \intset_ge(\result->key, keys(l)))
	_(ensures N(l) == \old(N(l)))
	_(ensures keys(l) == \old(keys(l)))
	_(ensures l != NULL ==> \result != NULL)
	_(ensures l != NULL ==> N(\result) == {\result})
	_(ensures l != NULL ==> \intset_in(\result->key, keys(l)))
	_(ensures l != NULL ==> keys(\result) == \intset_singleton(\result->key))

{
	_(assume mutable_list(l))
	if (l != NULL) {
		_(assume unfoldAllSort(l))

		while (l->next != NULL)
			_(invariant srtl(l))
			_(invariant srtl(\old(l)))
			_(invariant \subset(N(l), N(\old(l))))
			_(invariant \subset(lsegN(\old(l), l), N(\old(l))))
			_(invariant \srtlsegStar(\old(l), l))
			_(invariant \intset_ge(l->key, lsegk(\old(l), l)))
			_(invariant \intset_in(l->key, keys(l)))
			_(invariant l != NULL && mutable_list(l))
			_(invariant keys(l) == \intset_union(\intset_singleton(l->key), keys(l->next)))
		{ 
			_(assume unfoldMutable(l))
			_(assume unfoldAllSort(l))
			l = l->next;
			_(assume unfoldAllSort(l))
		}
		_(assert l != NULL && srtl(l))
		_(assert \intset_ge(l->key, keys(\old(l))))
	}
	return l;
}

Node * concat_sorted(Node * l1, Node * l2)
	_(requires srtl(l1) && srtl(l2) && \disjoint(N(l1), N(l2)))
	_(requires l2 != NULL ==> \intset_ge(l2->key, keys(l1)))
	_(ensures srtl(\result))
	_(ensures N(\result) == (\old(N(l1)) \union \old(N(l2))))
	_(ensures keys(\result) == \intset_union(\old(keys(l1)), \old(keys(l2))))
{
	_(ghost \objset G0 = (N(l1) \union N(l2)) ;)

	if (l2 != NULL) {
		if (l1 != NULL) {
			_(assume unfoldAllSort(l2)) // [!] (unfold-all-sort-l2-1)
			_(ghost \state S1 = \now())
			_(assert \disjoint(N(l1), N(l2)))
			_(assert \intset_ge(l2->key, keys(l1)))

			Node * last = find_last(l1);
			_(ghost \state S2 = \now())
			_(assume \disjoint(N(last), (G0 \diff \at(S1, N(l1)))))
			_(assume maintainsAcrossSort(l1, l2, S1, S2))
								
			_(assume unfoldAllSort(l2)) // [!] (unfold-all-sort-l2-2)

//			_(assert \intset_in(last->key, keys(l1))) // "moved" to postcondition of find_last
			_(assert \intset_ge(l2->key, keys(l1)))
			_(assert \intset_le(l2->key, keys(l2)))
			_(assert \intset_le(last->key, keys(l2)))

			_(assert srtl(last))
			_(assert \srtlsegStar(l1, last))
			//_(assert \disjoint(N(last), N(l2)))
			_(assume mutable_list(last))
			_(assert N(l1) == \old(N(l1)))
			_(assert N(l2) == \old(N(l2)))
			_(assert N(l1) == lsegN(l1, last) \union N(last))
			last->next = l2;
			_(ghost \state S3 = \now())
			_(assume unfoldAllSort(last))
			_(assume maintainsAcrossSort(last, l2, S2, S3))
			_(assume maintainsAcrossSrtlseg(last, l1, last, S2, S3))

			_(assert \intset_le(last->key, keys(l2)))
			_(assert srtl(last))

			_(assert N(last) == {last} \union N(l2))
			_(ghost LemmaSkip(l1, last) ;)
			_(assert N(l1) == lsegN(l1, last) \union N(last))
			//_(assert \disjoint(lsegN(l1, last), N(l2))) // (disj-lsegN-l1-last-l2) follows from (find-last-post-subset-lseg-l-res-l)
			                                              // otherwise it can be proved but not inferred, i.e., it would require assert
			//_(assert \disjoint(lsegN(l1, last), N(last)))
			_(assert \srtlsegStar(l1, last))
			_(assert srtl(l1))
			_(assert N(l2) == \old(N(l2)))
			_(assert N(l1) == \old(N(l1)) \union N(l2))
		} else {
			_(assert l1 == NULL)
			l1 = l2;
			_(assert srtl(l1))
			_(assert N(l1) == \old(N(l1)) \union N(l2))
		}
	} 
	_(assert N(l1) == \old(N(l1)) \union N(l2))
	return l1;
}



Node * quick_sort(Node * l)
	_(requires sll(l))
	//_(ensures keys(l) == \old(keys(l)))
	_(ensures N(\result) == \old(N(l)))
	_(ensures srtl(\result))
	_(ensures keys(\result) == \old(keys(l)))
{
	_(ghost \intset old_keys = keys(l))
	_(ghost \objset G0 = N(l) ;)

	if (l == NULL) {
		_(assert srtl(l))
		_(assert keys(l) == \old(keys(l)))
		_(assert N(l) == \old(N(l)))
		return l;
	} 

	_(assume mutable_list(l))
	Node * curr = l->next;
	_(assume unfoldMutable(l))
	_(assume unfoldAllSort(l))
	_(assert sll(curr))
	_(ghost \state S1 = \now() ;)

	int pivot = l->key;
	l->next = NULL;
	_(assume unfoldAll(l))
	//_(assert N(l) == {l})
	_(ghost \state S2 = \now() ;)
	_(assume maintainsAcross(l, curr, S1, S2))
	_(assert sll(curr))

	Node * lpt = NULL;
	Node * rpt = NULL;

	_(assert sll(curr))
	Node * tmp = curr;

	//_(assert \old(keys(l)) == \intset_union(keys(curr), \intset_singleton(pivot)))
	_(assert old_keys == \intset_union(keys(lpt), \intset_union(keys(rpt), \intset_union(keys(curr), \intset_singleton(pivot)))))
	while(curr != NULL)
		_(invariant \intset_le(pivot, keys(rpt)))
		_(invariant \intset_ge(pivot, keys(lpt)))
		_(invariant sll(tmp) && sll(curr))
		_(invariant sll(lpt) && sll(rpt))
		_(invariant \disjoint(N(lpt), N(rpt)))
		_(invariant \disjoint(N(rpt), N(curr)))
		_(invariant \disjoint(N(lpt), N(curr)))
		_(invariant !(l \in N(curr))) // [!] (inv-l-not-in-N-curr) shows (inv-l-not-in-N-lpt)  and (inv-l-not-in-N-rpt)
		_(invariant !(l \in N(rpt)))
		_(invariant !(l \in N(lpt)))
//		_(invariant \disjoint(N(lpt), N(tmp)))
//		_(invariant \disjoint(N(rpt), N(tmp)))
		_(invariant G0 == (N(lpt) \union N(rpt) \union N(curr) \union {l}))
		_(invariant curr == tmp)
		_(invariant old_keys == \intset_union(keys(lpt), \intset_union(keys(rpt), \intset_union(keys(curr), \intset_singleton(pivot)))))
		_(invariant mutable_list(curr))
	{
		_(assume unfoldMutable(curr))
		_(assume unfoldAllSort(curr))
		tmp = curr->next;
		_(assume unfoldAllSort(curr))
		if (curr->key <= pivot) {
			_(ghost \state S3 = \now())
			curr->next = lpt;
			_(assume unfoldAll(curr))
			_(ghost \state S4 = \now())
			_(assume maintainsAcross(curr, tmp,  S3, S4))
			_(assume maintainsAcross(curr, rpt,  S3, S4))
			_(assume maintainsAcross(lpt,  curr, S3, S4))
			_(assume maintainsAcross(lpt,  rpt,  S3, S4))
			lpt = curr;
			_(assert !(l \in N(lpt)))
		} else {		
			_(ghost \state S3 = \now())
			curr->next = rpt;
			_(assume unfoldAll(curr))
			_(ghost \state S4 = \now())
			_(assume maintainsAcross(curr, tmp,  S3, S4))
			_(assume maintainsAcross(curr, lpt,  S3, S4))
			_(assume maintainsAcross(rpt,  curr, S3, S4))
			_(assume maintainsAcross(rpt,  lpt,  S3, S4))
			rpt = curr;
		}

		curr = tmp;
	}
	_(ghost \state S5 = \now())
	_(assert curr == tmp)
	_(assert curr == NULL)
	_(assert sll(lpt))
	_(assert sll(rpt))
	_(assert \intset_le(pivot, keys(rpt)))
	_(assert \intset_ge(pivot, keys(lpt)))
	_(assert old_keys == \intset_union(keys(lpt), \intset_union(keys(rpt), \intset_union(keys(curr), \intset_singleton(pivot)))))
	_(assert keys(curr) == \intset_empty)
	_(assert old_keys == \intset_union(keys(lpt), \intset_union(keys(rpt), \intset_singleton(pivot))))

	l->next = rpt;
	_(ghost \state S6 = \now())
	_(assume unfoldAll(l))
	_(assume maintainsAcross(l, rpt, S5, S6))
	_(assume maintainsAcross(l, lpt, S5, S6))
	_(assert sll(rpt))
	_(assert keys(l) == \intset_union(keys(rpt), \intset_singleton(pivot)))
	_(assert old_keys == \intset_union(keys(lpt), keys(l)))
	_(assert sll(lpt) && sll(l))
	_(assert \intset_le(l->key, keys(l)))
	_(assert \intset_ge(l->key, keys(lpt)))
	_(assert \disjoint(N(l), N(lpt)))
	_(assert lpt != NULL ==> !(lpt \in N(l)))
	
	Node * t2 = quick_sort(l);
	_(ghost \state S7 = \now())
	_(assume \disjoint(N(t2), (G0 \diff \at(S6, N(l)))))
	_(ghost \objset G1 = N(t2) \union (G0 \diff \at(S6, N(l))) ;)
	_(assume maintainsAcrossSort(l, lpt, S6, S7))
	_(assert sll(lpt))
	_(assert keys(t2) == \at(S6, keys(l)))
	_(assert \disjoint(N(t2), N(lpt)))

	if (lpt == NULL) {
		//_(assert N(t2) == G0)
		//_(assert srtl(t2))
		return t2;
	}
	_(assert lpt != NULL ==> !(lpt \in N(t2)))
	_(assert old_keys == \intset_union(keys(lpt), keys(t2)))
	Node * t1 = quick_sort(lpt);
	_(ghost \state S8 = \now())
	_(assume \disjoint(N(t1), (G0 \diff \at(S7, N(lpt)))))
	//_(ghost G1 = N(t1) \union
	_(assume maintainsAcrossSort(lpt, t2, S7, S8))
	//_(assume maintainsAcrossSort(t2, t1, S7, S8))
	_(assert keys(t1) == \at(S7, keys(lpt)))

	_(assert old_keys == \intset_union(keys(t1), keys(t2)))
	_(assert srtl(t1))
	_(assert srtl(t2))
	_(assert \disjoint(N(t1), N(t2)))
	_(assert t2 != NULL ==> \intset_ge(t2->key, keys(t1)))
	_(assert G0 == N(t1) \union N(t2))
	_(assert old_keys == \intset_union(keys(t1), keys(t2)))
	return concat_sorted(t1, t2);
	//return concat_sorted(quick_sort(lpt), quick_sort(rpt));
}
