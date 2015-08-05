#include <vcc.h>

#include "../../dryad_list_defs.h"

_(def void \useLseg(\object b, \object e) 
	_(requires lseg(b, e) && \disjoint(N(e), lsegN(b, e)))
	{/* notifies dryad transformer about the list segment */}
	;)

_(logic \bool unchangedSll(\object o) = {:split} sll(o) && N(o) == \old(N(o)) ;)
_(logic \bool \sllStar (\object o1, \object o2) = {:split} sll(o1)  && sll(o2)  && \disjoint(N(o1), N(o2)) ;)
_(logic \bool \srtlStar(\object o1, \object o2) = {:split} srtl(o1) && srtl(o2) && \disjoint(N(o1), N(o2)) ;)
_(logic \bool \lsegStar(\object b,  \object  e) = {:split} lseg(b, e) && \disjoint(lsegN(b, e), N(e)) ;)
_(logic \bool \srtlsegStar(\object b,  \object  e) = {:split} srtlseg(b, e) && \disjoint(lsegN(b, e), N(e)) ;)

typedef
struct node {
	int key;
	struct node * next;
} Node;

typedef unsigned uint;

// TODO: should this be moved to dryad_list_defs?
_(logic \bool mutable_list(Node * x) =
	x != NULL ==> \mutable(x) && \writable(x))

_(logic \bool unfoldMutable(Node * x) =
	((x != NULL && x->next != NULL)
	==> (\mutable(x) == \mutable(x->next) &&
	     \writable(x) == \writable(x->next)) ) )

_(def void LemmaSkip(Node * b, Node * e)
	_(requires sll(b) && sll(e) && lseg(b, e))
	_(ensures N(b) == lsegN(b, e) \union N(e))
	_(ensures llen(b) == (lseglen(b, e) + llen(e)))
	_(decreases llen(b))
{
	if (b == e) {
		return;
	} else {
		_(assume unfoldAll(b))
		_(assume unfoldAllLseg(b, e))
		LemmaSkip(b->next, e);
	}
})

_(def void LemmaSkipSort(Node * b, Node * e)
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
		LemmaSkipSort(b->next, e);
	}
} ;)



Node * g_slist_prepend(Node * list, int data)
	_(requires sll(list))
	_(ensures sll(\result))
	_(ensures keys(\result) == \intset_union(\old(keys(list)), \intset_singleton(data)))
{
	_(ghost \objset G0 = N(list))
	_(assume list != NULL ==> \mutable(list) && \writable(list))
	_(ghost \state S1 = \now())

	Node * new_list = (Node *) malloc(sizeof(Node));
	_(assume new_list != NULL)
	_(assume !(new_list \in G0))
	
	new_list->key = data;
	new_list->next = list;
	_(assume unfoldAll(list))
	_(assume unfoldAll(new_list))
	_(ghost \state S2 = \now())
	_(assume maintainsAcross(new_list, list, S1, S2))
	
	return new_list;
}


Node * g_slist_last(Node * list)
	_(requires sll(list))
	_(ensures unchangedSll(list)) // synt sugar for _(ensures  sll(list) && N(list) == \old(N(list)))
	_(ensures  sll(\result))
	//_(ensures  sll(list))
	_(ensures  keys(list) == \old(keys(list)))
	//_(ensures  list == NULL ==> \result == NULL)
	_(ensures  list != NULL ==> \result != NULL)
	_(ensures !(\result \in lsegN(list, \result)))
	_(ensures \lsegStar(list, \result))
	//_(ensures lseg(list, \result))
	//_(ensures \disjoint(N(\result), lsegN(list, \result)))
	_(ensures \subset(lsegN(list, \result), N(list)))
	_(ensures \result != NULL ==> keys(\result) == \intset_singleton(\result->key))
{
	// locs: list
	_(assume mutable_list(list))
	//_(assume list != NULL ==> \mutable(list) && \writable(list))
	if(list != NULL) {
		_(assume unfoldAll(list))

		//_(assert keys(list) == \intset_union(keys(list->next), \intset_singleton(list->key)))
		//_(assert \subset(lsegN(\old(list), list), \old(N(list))))
		_(ghost Node * tmp_list = list ;)
		while(list->next != NULL) 
			// locs: list, list->next
			// deref: list
			_(invariant sll(list))
			_(invariant sll(\old(list)))
			_(invariant \lsegStar(\old(list), list)) // lsegStar is syntactic sugar for the invs below
			//_(invariant lseg(\old(list), list))
			//_(invariant \disjoint(N(list), lsegN(\old(list), list)))
			_(invariant \subset(N(list), N(\old(list))))                 // (subs1)
			_(invariant \subset(lsegN(\old(list), list), N(\old(list)))) // (subs2) [follows from (subs1)]
			_(invariant keys(list) == \intset_union(keys(list->next), \intset_singleton(list->key)))
			_(invariant \mutable(list) && \writable(list))
		{
			_(assume unfoldAll(list))
			list = list->next;
			_(assume unfoldAll(list))
			_(assume \writable(list) && \mutable(list))
		}
//		_(assert \subset(lsegN(\old(list), list), N(\old(list))))
//		_(assert list->next == NULL)
	}
	return list;
}


Node * g_slist_concat (Node * list1, Node * list2)
	_(requires \sllStar(list1, list2))
	//_(requires sll(list1) && sll(list2) && \disjoint(N(list1), N(list2)))
	_(ensures sll(\result))
	_(ensures keys(list2) == \old(keys(list2)))
	_(ensures keys(\result) == \intset_union(\old(keys(list1)), keys(list2)))
{
	//_(assume list1 != NULL ==> \mutable(list1) && \writable(list1))
	// locs: list1, list2
	_(ghost \objset G0 = (N(list1) \union N(list2)) ;)

	if (list2 != NULL) 
	{
		if (list1 != NULL) 
		{
			// locs: list1, list2 
			// derefs: list1, list2
			_(ghost \state S0 = \now() ;)
			//_(assert \disjoint(N(list1), N(list2)))

			Node * last = g_slist_last(list1);
			// locs: last, list1, list2
			_(ghost \useLseg(list1, last) ;) // this can be avoided if g_slist_last postcondition can be analyzed
			_(assume mutable_list(last))
			_(ghost \state S1 = \now() ;)
			_(assume \disjoint(N(last), (G0 \diff \at(S0, N(list1)))))
//			_(assert sll(last))
//			_(assert lseg(list1, last))
//			_(assert \disjoint(N(last), lsegN(list1, last)))
//			_(assert !(last \in lsegN(list1, last)))

//			_(assume disjointMaintainsAcross(list2, list1, S0, S1))
			//_(assume maintainsAcross(list1, list2, S0, S1)) 
			_(assume maintainsAcross(last, list1, S0, S1)) 
			_(assume maintainsAcross(last, list2, S0, S1)) 

			//_(assert sll(list2))
			//_(assert sll(list1))
			//_(assert \disjoint(N(list1), N(list2)))
			//_(assert \subset(lsegN(list1, last), N(list1)))
			//_(assert \disjoint(N(list2), lsegN(list1, last)))
			//_(assert keys(list1) == \old(keys(list1))) // OK
			//_(assert keys(last) == \intset_singleton(last->key)) // OK

			//_(assert \disjoint(lsegN(list1, last), N(last)))
			
			last->next = list2;
			// locs: last->next, last, list1, list2
			// fp: last
			_(assume unfoldAll(last))
			//_(assume unfoldAllLseg(last, last->next))
			_(ghost \state S2 = \now() ;)
			_(assume maintainsAcross(last, list2, S1, S2))
			_(assume maintainsAcrossLseg(list2, list1, last, S1, S2))
			_(assume maintainsAcrossLseg(last, list1, last, S1, S2))
			//_(assert sll(list1))
			//_(assert keys(list1) == \intset_union(\old(keys(list1)), keys(list2)))


			//_(assert keys(last) == \intset_union(keys(list2), \intset_singleton(last->key)))
			//_(assert \intset_subset(\old(keys(list1)), keys(list1)))

			//_(assert keys(list1) == \intset_union(keys(last), keys(list1)))
			//_(assert keys(list1) == \intset_union(\intset_union(keys(last), keys(list2)), keys(list1)))
//			_(assert !(last \in N(list2)))
//			_(assert \subset(N(list2), N(last)))
//			_(assert \disjoint(N(list2), lsegN(list1, last)))
			//_(assert \disjoint(N(preLast), N(list2)))
			//_(assert \subset(N(list2), N(list1)))
//			_(assert \disjoint(N(last), lsegN(list1, last)))

//			_(assert sll(last))
//			_(assert sll(list1))
//			_(assert keys(list1) == \intset_union(\old(keys(list1)), keys(list2)))
		} else {
			list1 = list2;
		}
	}
	return list1;
}


Node * g_slist_append (Node * list, int data)
	_(requires sll(list))
	_(ensures sll(\result))
	_(ensures keys(\result) == \intset_union(\old(keys(list)), \intset_singleton(data)))
{
	// locs: list
	_(assume list != NULL ==> \mutable(list) && \writable(list))
	_(ghost \objset G0 = N(list))
	_(ghost \state S0 = \now())
	Node * new_list;
	// locs: list, new_list
	Node * last;
	// locs: list, new_list, last

	new_list = (Node *) malloc(sizeof(Node));
	_(assume !(new_list \in G0))
	_(ghost \objset G1 = G0 \union {new_list})
	_(ghost \state S0a = \now())
	_(assume maintainsAcross(new_list, list, S0, S0a))
	_(assume new_list != NULL)
	_(assert sll(list))

	new_list->key = data;
	new_list->next = NULL;
	// locs: list, new_list, last
	// derefs: new_list
	_(assume unfoldAll(new_list))
	_(ghost \state S1 = \now())
	_(assume maintainsAcross(new_list, list, S0, S1))
	
	_(assert sll(list))
	_(assert sll(new_list))

	// locs: list, new_list, last
	// derefs: new_list
	if (list != NULL) {
		// locs: list, new_list, last
		// derefs: list, new_list
		_(assume unfoldAll(new_list))
		_(assume unfoldAll(list))

		last = g_slist_last(list);
		_(ghost \useLseg(list, last) ;) // will be used to inform the transformer about (2), and (4)
		_(assume unfoldAll(new_list))
		_(assume unfoldAll(list))
		_(assume \mutable(last) && \writable(last))
		_(ghost \state S2 = \now())
		_(assume \disjoint(\at(S2, N(last)), (G1 \diff (\at(S1, N(list)))) ) )
		//_(assume maintainsAcross(list, new_list, S1, S2))

		_(assert last != NULL)
		_(assert sll(list))
		_(assert sll(new_list))
		_(assert keys(list) == \old(keys(list)))
		_(assert keys(last) == \intset_singleton(last->key))

		_(assert \disjoint(lsegN(list, last), N(last)))
		_(assert !(new_list \in lsegN(list, last)))

		last->next = new_list; 
		_(assume unfoldAll(new_list))
		_(assume unfoldAll(last))               // (1)
		_(assume unfoldAll(list))               // (2)
		_(ghost \state S3 = \now())
		//_(assume maintainsAcross(last, new_list, S2, S3)) // (3) this one can be used instead of unfolding
		_(assume maintainsAcrossLseg(new_list, list, last, S2, S3)) // (4) this is CRUCIAL

		_(assert sll(list))
		_(assert keys(list) == \intset_union(\old(keys(list)), \intset_singleton(data)))
		return list;
	} else {
		_(assert unfoldAll(new_list))
		_(assert sll(new_list))
		_(assert keys(new_list) == \intset_singleton(data))
		return new_list;
	}
}


Node * g_slist_insert(Node * list, int data, int pos)
	_(requires sll(list))
	_(ensures sll(\result))
	_(ensures keys(\result) == \intset_union(\old(keys(list)), \intset_singleton(data)))
{
	// locs: list
	if(pos < 0)
		return g_slist_append(list, data);
	else if (pos == 0)
		return g_slist_prepend(list, data);

	_(ghost \objset G0 = N(list))
	_(assume list != NULL ==> \mutable(list) && \writable(list))
	_(ghost \state S0 = \now())

	Node * prev_list;
	Node * tmp_list;
	Node * new_list;
	// locs: list, prev_list, tmp_list, new_list

	//_(assert sll(list))
	new_list = (Node *) malloc(sizeof(Node));
	_(assume new_list != NULL)
	_(assume !(new_list \in G0))
//	_(ghost \state S0a = \now() ;)
//	_(assume maintainsAcross(new_list, list, S0, S0a))
//	_(assert sll(list))

	new_list->key = data;
	// locs: list, prev_list, tmp_list, new_list
	// derefs: new_list
	//_(ghost \state S0b = \now() ;)
	//_(assume maintainsAcross(new_list, list, S0, S0b))
	//_(assert sll(list))

	if(list == NULL) {
		new_list->next = NULL;
		_(assume unfoldAll(new_list))
		_(assert sll(new_list))
		_(assert keys(new_list) == \intset_singleton(data))
		return new_list;
	}

	_(ghost \state S1 = \now())
	_(assume maintainsAcross(new_list, list, S0, S1))
	//_(assert sll(list))

	tmp_list = list;
	prev_list = tmp_list; // this modification makes verification much more elegant, and
	                      // preserves the semantics, since the loop always executes at least once
	//_(assert sll(list))
	//_(assert keys(list) == \old(keys(list)))
	//_(assert \mutable(tmp_list) && \writable(tmp_list))
	//_(assert pos > 0 && tmp_list != NULL)
	//_(assert sll(tmp_list))
	//_(assert \subset(lsegN(list, prev_list), N(list)))
	//_(assert \subset(N(prev_list), N(list)))

	// locs: list, prev_list, tmp_list, new_list
	// derefs: new_list, tmp_list
	while(pos > 0 && tmp_list != NULL)
		_(invariant prev_list == tmp_list || prev_list->next == tmp_list)
		_(invariant prev_list != tmp_list ==> prev_list->next == tmp_list)
		_(invariant pos >= 0)
		_(invariant sll(tmp_list))
		_(invariant sll(prev_list))
		_(invariant sll(list))
		_(invariant \lsegStar(list, tmp_list))   
		_(invariant \lsegStar(list, prev_list))
		_(invariant \subset(N(tmp_list), N(list)))  // (sub1)
		_(invariant \subset(N(prev_list), N(list))) // (sub2) depends on the (sub1)
		_(invariant !(new_list \in lsegN(list, tmp_list)))  // (nmemb1) shows (nmemb2)
		_(invariant !(new_list \in lsegN(list, prev_list))) // (nmemb2) follows from (nmemb1) shows (disj2)
		_(invariant prev_list != NULL && mutable_list(prev_list))
		_(invariant mutable_list(tmp_list))
	{
		_(assume unfoldMutable(tmp_list))
		pos--;
		prev_list = tmp_list;
		_(assume unfoldAll(tmp_list))
		tmp_list = tmp_list->next;
//		_(assume unfoldAll(tmp_list))
		//_(assume tmp_list != NULL ==> \mutable(tmp_list) && \writable(tmp_list))
	}
	_(ghost \state S2 = \now() ;)
	_(assert prev_list != NULL)
	_(assert sll(tmp_list) && sll(prev_list) && sll(list))
	_(assert \lsegStar(list, prev_list))

	_(assume unfoldAll(prev_list))  // theoretically, unfolding should be done here, 
									// but it can be also done after the assignment
	Node * tmp_prev = prev_list->next;
	// locs: list, prev_list, tmp_list, new_list
	// derefs: new_list, tmp_list, prev_list

	//_(assume unfoldAll(prev_list))
	//_(assume unfoldLseg(prev_list, prev_list->next))
	_(ghost \state S3 = \now() ;)

	_(assert \lsegStar(list, prev_list))
	_(assert \subset(N(prev_list), N(list)))
	_(assert sll(tmp_prev))
	_(assert !(new_list \in N(tmp_prev))) // follows from inv (sub2)
	_(assert !(new_list \in lsegN(list, prev_list))) // (nmemb) follows from inv (nmemb2)

	new_list->next = tmp_prev; 
	// locs: list, prev_list, tmp_list, new_list, tmp_prev
	// derefs: new_list, tmp_list, prev_list
	_(assume unfoldAll(new_list))
	_(assume unfoldAll(prev_list))
	_(assume unfoldAll(tmp_list))

	_(ghost \state S4 = \now() ;)
	_(assume maintainsAcross(new_list, tmp_prev, S3, S4)) // necessary to show that tmp_prev does not change
	_(assume maintainsAcrossLseg(tmp_prev, list, new_list, S3, S4)) // necessary to show that segment list ~> new_list does not change

	//_(assume maintainsAcross(new_list, list, S3, S4)) //  [shows sll(list)]
	//_(assume maintainsAcrossLseg(new_list, list, prev_list, S3, S4))
	// maintain the other segments w.r.t. new_list
	_(assume maintainsAcrossLseg(new_list, list, prev_list, S3, S4))
	_(assume maintainsAcrossLseg(new_list, list, tmp_list, S3, S4))

	_(assert sll(new_list) && sll(prev_list) && sll(list))
	_(assert !(new_list \in N(prev_list)))
	_(assert !(new_list \in N(tmp_prev)))
	_(assert \disjoint(lsegN(list, prev_list), N(prev_list)))

	_(assert sll(new_list))
	_(assert !(new_list \in N(prev_list->next)))
	_(assert !(new_list \in lsegN(list, prev_list))) // (nmemb) follows from inv (nmemb2)
	_(assert !(prev_list \in N(new_list)))
	_(assert \lsegStar(list, prev_list))

	prev_list->next = new_list;
	_(assume unfoldAll(prev_list))
	//_(assume unfoldAll(new_list))
	_(assume unfoldAll(tmp_list))
	_(ghost \state S5 = \now())
	// ---------------------------------------------------------------------------------------
	// the two maintains below are kind of "symmetrical"
	// can be necessary to show that the assignment does not introduce cycles
	_(assume maintainsAcross(prev_list, new_list, S4, S5)) // (maint2) [shows sll(new_list)]
	_(assume maintainsAcrossLseg(new_list, list, prev_list, S4, S5))
	// ---------------------------------------------------------------------------------------
	// maintain the other (sub) lists [the node representing the head of the list should not be maintained]
	_(assume maintainsAcross(prev_list, tmp_list, S4, S5))
	// maintain the other segments w.r.t. to the prev_list
	_(assume maintainsAcrossLseg(prev_list, list, prev_list, S4, S5))
	_(assume maintainsAcrossLseg(prev_list, list, tmp_list, S4, S5))

	_(assert \subset(N(new_list), N(prev_list)))
	_(assert \disjoint(lsegN(list, prev_list), N(prev_list))) // (disj) [follows from (nmemb)]
	_(assert \lsegStar(list, prev_list))  // (lseg1) [follows from (disj)]
	_(assert \lsegStar(list, new_list))  //  (lseg2) [follows from (lseg1)]
	_(assert sll(new_list) && sll(prev_list))

	_(assert sll(list))
	return list;			
}


Node * g_slist_insert_before (Node * slist, Node * sibling, int data)
	_(requires sll(slist))
	_(requires sll(sibling))
	_(requires \lsegStar(slist, sibling))
	_(ensures sll(slist))
	_(ensures sll(\result))
	_(ensures keys(\result) == \intset_union(\old(keys(slist)), \intset_singleton(data)))
{
	if (slist == NULL) {
		slist = (Node *) malloc (sizeof(Node));
		_(assume slist != NULL)
		slist->key = data;
		slist->next = NULL;
		_(assume unfoldAll(slist))

		//_(assert sll(slist))
		//_(assert keys(slist) == \intset_union(\old(keys(slist)), \intset_singleton(data))) // (keys)
		//_(assert keys(slist) == \intset_singleton(data)) // stronger version of (keys)
		return slist;
	} else {
		_(ghost \objset G0 = N(slist) ;)
		_(assume mutable_list(slist))
		// hd: slist
		// locs: slist, sibling, node, last
		Node * node, * last = NULL;

		//_(assert slist != NULL && last == NULL)
		node = slist;

		//_(assert \subset(lsegN(slist, node), N(slist)))
		//_(assert sll(node))
		//_(assert node == slist <==> last == NULL)
		// locs: slist, sibling, node, last
		while (node != NULL && node != sibling)
			//_(invariant node == slist <==> last == NULL)     // may be needed to prove stronger postconditions
			//_(invariant last != NULL ==> last->next == node) // may be needed to prove stronger postconditions
			_(invariant sll(node))  // (sll1) 
			_(invariant sll(last))  // (sll2) [follows from (sll1)]
			_(invariant \lsegStar(slist, node))  // (lseg*1) 
			_(invariant \lsegStar(slist, last))  // (lseg*2) [follows from (lseg*1)]
			_(invariant \subset(N(node), N(slist))) // (subs1)
			_(invariant \subset(N(last), N(slist))) // (subs2) [follows from (subs1)]
			_(invariant \subset(lsegN(slist, node), N(slist))) // (subs3) [follows from (subs1)]
			_(invariant \subset(lsegN(slist, last), N(slist))) // (subs4) [follows from (subs3)]
			_(invariant mutable_list(node)) // (mw1)
			_(invariant mutable_list(last)) // (mw2) [follows from (mw1)]
		{
//			_(assume unfoldAll(node))
			//_(assume unfoldAllLseg(slist, node)) // [???]
			last = node;
			_(assume unfoldAll(last))
			node = last->next;
			_(assume node != NULL ==> \mutable(node) && \writable(node))
		}
		//_(assert G0 == N(slist))

		if (last == NULL) {
			// locs: slist, sibling, node, last
			// derefs: last (node)
			// lsegs: slist~>node, slist~>last
			_(ghost \state S0 = \now())

			node = (Node *) malloc (sizeof(Node));
			_(assume node != NULL)
			_(assume !(node \in G0))

			node->key = data;
			node->next = slist;
			_(assume unfoldAll(node))
			_(ghost \state S1 = \now())
			_(assume maintainsAcross(node, slist, S0, S1))
			// other locs (would be generated automatically, but are not relevant for the property)
			_(assume maintainsAcross(node, sibling, S0, S1))
			_(assume maintainsAcross(node, last, S0, S1))


			//_(assert sll(node))
			//_(assert keys(node) == \intset_union(\old(keys(slist)), \intset_singleton(data)))
			return node;
		} 
		else {
			//_(assert last != NULL <==> (node == NULL || (node == sibling && node != slist)))
			//_(assert last->next == node)

			// locs: slist, sibling, node, last
			// derefs: last (node)
			// lsegs: slist~>node, slist~>last

			// unfold all derefs
			_(assume unfoldAll(last))
			_(ghost \state S0 = \now() ;)

			node = (Node *) malloc (sizeof(Node));
			_(assume node != NULL)
			_(assume !(node \in G0))
			//_(assert G0 == N(slist))
			_(ghost \state S1 = \now() ;)
			_(assume maintainsAcross(node, slist, S0, S1))
			_(assume maintainsAcross(node, last , S0, S1))
			_(assume maintainsAcrossLseg(node, slist, last, S0, S1)) // this is necessary!!

			_(assume unfoldAll(last))
			Node * tmp_last = last->next;
			_(ghost \state S2 = \now())

			// locs: slist, sibling, node, last
			// derefs: node, last
			// derefs: slist~>node, slist~>last
			node->key = data;
			node->next = tmp_last;
			_(assume unfoldAll(node))
			_(ghost \state S3 = \now())
			_(assume maintainsAcross(node, tmp_last, S2, S3))
			_(assume maintainsAcrossLseg(tmp_last, slist, node, S2, S3))
			_(assume maintainsAcross(node, last, S2, S3))
			_(assume maintainsAcross(node, slist, S2, S3))
			_(assume maintainsAcrossLseg(node, slist, last, S2, S3))

			last->next = node;
			_(assume unfoldAll(last))
			_(ghost \state S4 = \now())
			// --------------------------------------------------------
			// no cycles 
			_(assume maintainsAcross(last, node, S3, S4))
			_(assume maintainsAcrossLseg(node, slist, last, S3, S4))
			// --------------------------------------------------------
			// not necessary, but would generated automatically
			_(assume maintainsAcross(last, slist, S3, S4))
			_(assume maintainsAcrossLseg(last, slist, node, S3, S4))
			 
			//_(assert sll(node) && sll(last))
			
			//_(assert sll(slist))
			//_(assert keys(slist) == \intset_union(\old(keys(slist)), \intset_singleton(data)))
			return slist;
		}
	}
}

Node * g_slist_remove (Node * list, int data)
	_(requires sll(list))
	_(ensures  sll(\result))
	//_(ensures !\intset_in(data, \old(keys(list))) ==> (keys(\result) == \old(keys(list))))
	//_(ensures  \intset_in(data, \old(keys(list))) ==> (keys(\result) == \intset_diff(\old(keys(list)), \intset_singleton(data)) ))
	// a bag (multiset) is needed to to prove the stronger property
	_(ensures !\intbag_in(data, \old(keyb(list))) ==> (keyb(\result) == \old(keyb(list))))
	_(ensures  \intbag_in(data, \old(keyb(list))) ==> (keyb(\result) == \intbag_diff(\old(keyb(list)), \intbag_singleton(data))))
{
	_(assume mutable_list(list))
	_(ghost \objset G0 = N(list))
	_(assume list != NULL ==> \malloc_root(list))

	// locs: tmp, prev, list
	Node *tmp, *prev = NULL;

	tmp = list;
	_(assert N(list) == lsegN(list, tmp) \union N(tmp))
	while(tmp != NULL)
		_(invariant sll(tmp))
		_(invariant sll(prev))
		_(invariant \lsegStar(list, tmp))  // lseg(list,tmp)
		_(invariant \lsegStar(list, prev)) // lseg(list, prev)
		_(invariant \subset(N(tmp), N(list)))
		_(invariant \subset(N(prev), N(list)))
		_(invariant prev == NULL ==> tmp == list)
		_(invariant prev != NULL ==> prev->next == tmp)
		_(invariant N(list) == lsegN(list, tmp) \union N(tmp))
		_(invariant keyb(list) == \old(keyb(list)))
		_(invariant !\intbag_in(data, lsegb(list, tmp)))
		_(invariant tmp  != NULL ==> \malloc_root(tmp))
		_(invariant mutable_list(tmp))
		_(invariant mutable_list(prev))
	{
		_(assume unfoldAll(tmp))
		_(assume unfoldAll(prev))
		
		//_(assert prev != NULL ==> !(prev \in N(tmp)))
		if (tmp->key == data)
		{
			// locs: tmp, prev, list
			// derefs: tmp
			_(assert \intset_in(data, keys(tmp)))
			_(assert \intset_in(data, keys(list)))

			_(assume unfoldAll(tmp))
			// locs: tmp, prev, list, tmp_next
			// derefs: tmp
			// lseg: list~>tmp, list~>prev
			Node * tmp_next = tmp->next;
			//_(assert prev != NULL ==> !(prev \in N(tmp)))
			_(ghost \state S1 = \now())
			
			_(assert N(list) == lsegN(list, prev) \union N(prev))
			_(assert N(list) == lsegN(list, tmp)  \union N(tmp))

			if (prev != NULL) {
				// locs: tmp, prev, list, tmp_next
				// derefs: tmp
				// lseg: list~>tmp, list~>prev
				_(assert !(prev \in N(tmp)))
				_(assert \lsegStar(list, prev))
				_(assert \lsegStar(list, tmp))

				prev->next = tmp_next;
				_(assume unfoldAll(prev))
				_(assume unfoldAll(tmp))
				_(ghost \state S2 = \now())
				// ----------------------------------------------------------
				// no-cycles
				_(assume maintainsAcross(prev, tmp_next, S1, S2))
				_(assume maintainsAcrossLseg(tmp_next, list, prev, S1, S2))
				// ----------------------------------------------------------
				_(assume maintainsAcrossLseg(prev, list, prev, S1, S2))

				_(assert sll(tmp_next) && sll(prev))
				_(assert \lsegStar(list, prev))

				_(assert !(tmp \in N(prev)))
				_(assert !(tmp \in lsegN(list, prev)))

				_(assert N(prev) == {prev} \union N(tmp_next))

				_(assert sll(list))
			} else {
				
				list = tmp_next;
				_(assert sll(tmp_next))
				_(assert sll(list))
				_(assert !(tmp \in N(list)))
				_(assert keyb(list) == \intbag_diff(\old(keyb(list)), \intbag_singleton(data)))
				_(assert tmp \in \old(N(list)))
				_(assert N(list) == \old(N(list)) \diff {tmp})
				//_(assert 
			}
			_(assert keyb(list) == \intbag_diff(\old(keyb(list)), \intbag_singleton(data)))

			_(ghost \state S3 = \now())
			_(assert !(tmp \in N(prev)))
			_(assert !(tmp \in lsegN(list, prev)))
			_(assert \lsegStar(list, prev))

			_(assert sll(list))
			_(assert keyb(list) == \intbag_diff(\old(keyb(list)), \intbag_singleton(data)))
			free(tmp);
			_(ghost \state S4 = \now())
			_(assume maintainsAcross(tmp, prev, S3, S4))			 // [maint-prev]
			_(assume maintainsAcross(tmp, list, S3, S4))

			_(assume maintainsAcrossLseg(tmp, list, prev, S3, S4))   // [maint-lseg-list-prev]
			_(assume maintainsAcrossLseg(tmp, list, tmp, S3, S4))

			_(assert sll(prev))              // [sll-prev] follows from [maint-prev]
			_(assert \lsegStar(list, prev))  //  [lseg*-list-prev] follows from  [maint-lseg-list-prev]
			_(assert sll(list))              // follows from  [sll-prev] and [lseg*-list-prev]
			_(assert keyb(list) == \intbag_diff(\old(keyb(list)), \intbag_singleton(data)))
			break;
		}
		
		prev = tmp;
		_(assume unfoldAll(prev))
		tmp = prev->next;

		_(assume tmp != NULL ==> \malloc_root(tmp))
		_(assume tmp != NULL ==> \mutable(tmp) && \writable(tmp))
	}
	_(assert sll(list))
	//_(assert \intbag_in(data, \old(keyb(list))) ==> keyb(list) == \intbag_diff(\old(keyb(list)), \intbag_singleton(data)))
	return list;
}


Node * g_slist_remove_all(Node * list, int data)
	_(requires sll(list))
	_(ensures  sll(\result))
	_(ensures !\intset_in(data, \old(keys(list))) ==> (keys(\result) == \old(keys(list))))
	_(ensures !\intset_in(data, keys(\result)))
	//_(ensures  \intset_in(data, \old(keys(list))) ==> (keys(\result) == \intset_diff(\old(keys(list)), \intset_singleton(data))))

{
	_(assume list != NULL ==> \mutable(list) && \writable(list) && \malloc_root(list))
	Node *tmp, *prev = NULL;

	tmp = list;
	_(assert keys(list) == \intset_union(lsegk(list, tmp), keys(tmp)))

	// locs: list, tmp, prev
	// derefs: tmp
	while(tmp != NULL)
		_(invariant sll(tmp) && sll(prev) && sll(list))
		_(invariant \lsegStar(list, tmp))
		_(invariant \lsegStar(list, prev))
		_(invariant !\intset_in(data, \old(keys(list))) ==> (keys(list) == \old(keys(list))))
		_(invariant !\intset_in(data, lsegk(list, tmp)))
		_(invariant \intset_in(data, \old(keys(list))) ==> (\intset_in(data, keys(list)) || !\intset_in(data, keys(list)))) 

		_(invariant \intset_in(data, keys(tmp)) <==> \intset_in(data, keys(list)))
		//_(invariant keys(list) == \old(keys(list)) || keys(list) == \intset_diff(\old(keys(list)), delk))
		//_(invariant (\intset_in(data, \old(keys(list))) && keys(list) != \old(keys(list))) ==> (\intset_diff(\old(keys(list)), keys(list)) == \intset_singleton(data)))
		_(invariant keys(list) == \intset_union(lsegk(list, tmp), keys(tmp)))
		_(invariant prev != NULL ==> prev->next == tmp)
		_(invariant tmp  != NULL ==> \mutable(tmp) && \writable(tmp) && \malloc_root(tmp))
		_(invariant prev != NULL ==> \mutable(prev) && \writable(prev))
	{

		if (tmp->key == data)
		{
			_(assert \intset_in(data, keys(tmp)))
			_(assert !\intset_in(data, lsegk(list, tmp)))

			_(assert sll(tmp) && sll(prev) && sll(list))
			_(assert \lsegStar(list, tmp))
			_(assert \lsegStar(list, prev))

			_(assume unfoldAll(tmp))
			_(ghost \state S1 = \now() ;)
			Node * tmp_next = tmp->next;
			_(assert sll(tmp_next))
			_(assert sll(tmp) && sll(prev) && sll(list))
			_(assert \intset_in(data, lsegk(list, tmp_next)))

			if (prev != NULL) {
				_(assume unfoldAll(prev))
				_(assume unfoldAll(tmp))
				_(ghost \state S2 = \now() ;)

				// locs: list, tmp, prev, tmp_next
				// derefs: tmp, prev
				prev->next = tmp_next;
				_(assume unfoldAll(prev))
				_(ghost \state S3 = \now() ;)
				// ---------------------------------------------------------
				_(assume maintainsAcross(prev, tmp_next, S2, S3))
				_(assume maintainsAcrossLseg(tmp_next, list, prev, S2, S3))
				// ---------------------------------------------------------
				_(assume maintainsAcross(prev, tmp, S2, S3))
				_(assume maintainsAcrossLseg(prev, list, prev, S2, S3))
				_(assume maintainsAcrossLseg(prev, list, tmp, S2, S3))
				_(assume maintainsAcrossLseg(prev, list, tmp_next, S2, S3))
				// ---------------------------------------------------------
				_(assert sll(prev))
				_(assert \lsegStar(list, prev))
				_(assert sll(tmp_next))
				_(assert \lsegStar(list, tmp_next))
				
			} else {
				list = tmp_next;
				_(assert sll(tmp) && sll(prev) && sll(list))
				//_(assert \lsegStar(list, tmp_next))
			}

			_(ghost \state S4 = \now() ;)
			_(assert sll(prev))
			_(assert \lsegStar(list, prev))
			_(assert sll(tmp_next))
			_(assert \lsegStar(list, tmp_next))
			_(assert !(tmp \in N(prev)))
			_(assert !(tmp \in lsegN(list, prev)))

			//_(assert tmp->key == data)
			free(tmp);
			_(ghost \state S5 = \now() ;)
			_(assume maintainsAcross(tmp, prev, S4, S5))
			_(assume maintainsAcross(tmp, tmp_next, S4, S5))
			_(assume maintainsAcross(tmp, list, S4, S5))
			_(assume maintainsAcrossLseg(tmp, list, prev, S4, S5))
			//_(assume maintainsAcrossLseg(tmp, list, tmp, S4, S5))
			//_(assume maintainsAcrossLseg(tmp, list, tmp_next, S4, S5))

			_(assert sll(prev))
			_(assert \lsegStar(list, prev))
			_(assert sll(tmp_next))
			_(assert \lsegStar(list, tmp_next))

			tmp = tmp_next;

			_(assert sll(tmp))
			_(assert \lsegStar(list, tmp))
			_(assert sll(prev))

			_(assert \lsegStar(list, prev))
			_(assert sll(list))
			_(assert !\intset_in(data, lsegk(list, tmp)))
		} else {
			prev = tmp;
			_(assume unfoldAll(prev))
			tmp = prev->next;

			_(assert sll(tmp) && sll(prev) && sll(list))
		}
		
		_(assume tmp != NULL ==> \mutable(tmp) && \writable(tmp) && \malloc_root(tmp))
	}
	_(assert !\intset_in(data, keys(list)))
	return list;
}


//_(def void LemmaSkip(Node * b, Node * e)
//	_(requires sll(b) && sll(e) && lseg(b, e))
//	_(ensures N(b) == lsegN(b, e) \union N(e))
//	_(decreases llen(b))
//{
//	if (b == e) {
//		return;
//	} else {
//		_(assume unfoldAll(b))
//		_(assume unfoldAllLseg(b, e))
//		LemmaSkip(b->next, e);
//	}
//})

Node * g_slist_remove_link(Node * list, Node * link)
	_(requires sll(list))
	_(requires sll(link) && \malloc_root(link)) // g_slist_delete link needs to know that 'link' can be freed
	_(ensures sll(\result)) 
	_(ensures sll(link) && \malloc_root(link)) // g_slist_delete_link needs to know that 'link' remains malloced
	_(ensures !(link \in \old(N(list))) ==> \old(N(list)) == N(\result)) // (POST-NO-CHANGE)
	//_(ensures  link \in \old(N(list)) ==> !(link \in N(\result))) // (POST-NO-LINK)
	_(ensures   link \in \old(N(list)) ==> (N(\result) == (\old(N(list)) \diff {link}))) // (POST-NO-LINK)
{
	_(assume list != NULL ==> \mutable(list) && \writable(list))
	Node * tmp;
	Node * prev;

	prev = NULL;
	tmp = list;

	// locs: list, link, tmp, prev
	// derefs: tmp
	// lseg: list~>prev, list~>tmp
	while(tmp != NULL)
		_(invariant sll(prev))
		_(invariant sll(tmp))
		_(invariant sll(list))
		_(invariant \lsegStar(list, prev)) // generate LemmaSkip
		_(invariant \lsegStar(list, tmp))
		_(invariant N(list) == lsegN(list, prev) \union N(prev))
		_(invariant N(list) == lsegN(list, tmp) \union N(tmp))
		_(invariant N(list) == \old(N(list)))
		//_(invariant !(link \in \old(N(list))) ==> \old(N(list)) == N(list))
		_(invariant \subset(N(prev), N(list)))
		_(invariant \subset(N(tmp), N(list))) // (sub-tmp-list) shows (link-in-list)
		_(invariant !(link \in lsegN(list, tmp))) // shows (POST-NO-LINK)
		// _(invariant link \in N(tmp) ==> link->next == NULL)
		_(invariant prev == NULL ==> tmp == list)
		_(invariant prev != NULL ==> prev->next == tmp) // (prev-tmp) shows (non-memb-prev)
		_(invariant prev != NULL ==> \mutable(prev) && \writable(prev))
		_(invariant tmp != NULL ==> \mutable(tmp) && \writable(tmp))
		_(invariant \malloc_root(link))
	{
		_(assume unfoldAll(tmp))
		if (tmp == link)
		{
			_(assert N(list) == lsegN(list, prev) \union N(prev))
			_(assert (link \in N(list))) // (link-in-list) shows (POST-NO-CHANGE), follows from (sub-tmp-list)

			_(assume unfoldAll(tmp))
			Node * tmp_next = tmp->next;
			_(ghost \state S1 = \now())
			_(assert !(link \in N(tmp_next)))

			if (prev != NULL) {
				_(assume unfoldAll(prev))
				
				_(assert N(list) == (lsegN(list, prev) \union N(prev)))
				_(assert \subset(lsegN(list, prev), N(list)))
				_(assert \subset(N(prev), N(list)))

				_(assert keys(list) == \intset_union(lsegk(list, prev), keys(prev)))

				_(assert N(prev) == N(list) \diff lsegN(list, prev))
				_(assert sll(tmp_next))
				_(assert !(prev \in N(tmp_next))) // (non-memb-prev) follows from (prev-tmp)
				_(assert !(link \in N(tmp_next)))
				// locs: list, link, tmp, prev, tmp_next
				// derefs: tmp
				// lseg: list~>prev, list~>tmp
				prev->next = tmp_next;
				_(assume unfoldAll(prev))
				_(ghost \state S2 = \now())
				// ---------------------------------------------------------
				_(assume maintainsAcross(prev, tmp_next, S1, S2))
				_(assume maintainsAcrossLseg(tmp_next, list, prev, S1, S2))
				// ---------------------------------------------------------
				_(assume maintainsAcross(prev, list, S1, S2))
				_(assume maintainsAcross(prev, link, S1, S2))
				_(assume maintainsAcross(prev, tmp, S1, S2))
				_(assume maintainsAcross(prev, tmp_next, S1, S2))
				_(assume maintainsAcrossLseg(prev, list, prev, S1, S2)) // (maint-lseg) shows (sll-list-1)
				_(assume maintainsAcrossLseg(prev, list, tmp, S1, S2))
				_(assume maintainsAcrossLseg(prev, list, link, S1, S2))

				_(assert sll(list)) // (sll-list-1) follows from (main-lseg)
				_(assert N(prev) == \at(S1, N(prev)) \diff {link})
				_(assert lsegN(list, tmp_next) == \at(S1, lsegN(list, tmp_next)) \diff {link})
//				_(assert N(list) == \at(S1, N(list)) \diff {link})
				_(assert lsegN(list, prev) == \at(S1, lsegN(list, prev)))
				_(assert !(tmp \in N(prev))) 
				_(assert keys(list) == \intset_union(lsegk(list, prev), keys(prev)))

				//_(assert N(list) == (lsegN(list, prev) \union N(prev)))   
				_(ghost LemmaSkip(list, prev))

				_(assert N(list) == (lsegN(list, prev) \union N(prev)))   
				//_(assert N(list) == lsegN(list, tmp) \union N(tmp))
				_(assert N(list) == \old(N(list)) \diff {link})
			} else {
				_(assert N(list) == \old(N(list)))
				_(assert list == link)
				list = tmp_next;
				_(assert sll(list))
				_(assert N(list) == \old(N(list)) \diff {link})
			}

			_(ghost \state S3 = \now())
			_(assert sll(list))
			_(assert !(tmp \in N(prev)))
			_(assert !(link \in N(list)))
			_(assert N(list) == \old(N(list)) \diff {link})

			// locs: list, link, tmp, prev, tmp_next
			// derefs: tmp
			// lseg: list~>prev, list~>tmp
			tmp->next = NULL;
			_(assume unfoldAll(tmp))
			_(ghost \state S4 = \now())
			_(assume maintainsAcross(tmp, prev, S3, S4))            // (maint-tmp-prev)
			_(assume maintainsAcross(tmp, list, S3, S4))
			_(assume maintainsAcross(tmp, tmp_next, S3, S4))
			_(assume maintainsAcrossLseg(tmp, list, prev, S3, S4))  // (maint-lseg-list-prev)
			_(assume maintainsAcrossLseg(tmp, list, tmp, S3, S4))

			_(assert sll(tmp))
			_(assert sll(prev))             // (sll-prev) follows from (maint-tmp-prev)
			_(assert \lsegStar(list, prev)) // (lseg-list-prev) follows from (maint-lseg-list-prev)
			_(assert sll(list))             // (sll-list-2) follows-from (sll-prev) and (lseg-list-prev)
			_(assert link->next == NULL)
			_(assert !(link \in lsegN(list, prev)))
			_(assert !(link \in N(prev)))
			//_(assert N(list) == lsegN(list, prev) \union N(prev))
			_(assert N(list) == \old(N(list)) \diff {link})
			break;	
		}
		prev = tmp;
		_(assume unfoldAll(tmp))
		tmp = tmp->next;
		_(assume tmp != NULL ==> \mutable(tmp) && \writable(tmp))
	}
	_(assert sll(list))
	_(assert sll(link))
	return list;
}


Node * g_slist_delete_link(Node * list, Node * link_)
	_(requires sll(list))
	_(requires sll(link_) && \malloc_root(link_))
	_(ensures sll(\result))
	_(ensures !(link_ \in \old(N(list))) ==> \old(N(list)) == N(\result)) // (POST-NO-CHANGE)
	_(ensures   link_ \in \old(N(list)) ==> (N(\result) == (\old(N(list)) \diff {link_}))) // (POST-NO-LINK)
	//_(ensures sll(link_)) // compared to g_slist_remove_link, this, as expected, cannot be proved
{
	_(assert \malloc_root(link_))
	_(assume \mutable(link_) && \writable(link_))
	list = g_slist_remove_link(list, link_);
	_(assert \malloc_root(link_))
	_(assert link_->\valid)

	_(ghost \state S1 = \now())
	free(link_); // VCC does not have a clear semantics of free
	             // in particular, I couldn't find guarantees of free
	_(ghost \state S2 = \now())
	_(assume maintainsAcross(link_, list, S1, S2))

	return list;
}

// copying reduces to successive appending to 
// the tail of the new list, that is not how the original 
// glib copy was written, so I've modified it to reflect the above idea
Node * g_slist_copy(Node * list)
	_(requires sll(list))
	_(ensures \sllStar(list, \result))
	_(ensures keys(\result) == keys(list)) // (POST-KEYS)

{
	_(assume mutable_list(list))
	_(ghost \objset G0 = N(list))
	_(ghost \objset G1 = G0)

	Node * new_list = NULL;
	// locs: new_list, list
	if (list != NULL) {
		Node * last = NULL;
		//\useLseg(list, last)
		// locs: new_list, list, last

		_(ghost \state S1 = \now())
		new_list = (Node *) malloc(sizeof(Node));
		_(assume new_list != NULL)
		_(assume !(new_list \in G0))
		_(ghost G1 = G1 \union {new_list})
//		_(ghost \state S1a = \now())
//		_(assume maintainsAcross(new_list, list, S1, S1a))
//		_(assume maintainsAcross(new_list, last, S1, S1a))

		_(assume unfoldAll(list))
		new_list->key = list->key;
		new_list->next = NULL; // not in the original version (check if it can be removed later)
		_(assume unfoldAll(new_list))
		_(ghost \state S2 = \now())
		_(assume maintainsAcross(new_list, list, S1, S2))
		_(assume maintainsAcross(new_list, last, S1, S2))

		last = new_list;

		_(assume unfoldMutable(list))
		_(assume unfoldAll(list))
		_(assume unfoldAllLseg(list, list->next)) // (unfold-lseg-old) [shows (lseg-keys-old)]
		list = list->next; // argument update/dereference seems to be needing special handling

		_(assert sll(list))
		_(assert keys(new_list) == \intset_singleton(\old(list)->key))
		_(assert keys(new_list) == lsegk(\old(list), list)) // (lseg-keys-old) [follows from (unfold-lseg-old)]

		_(assert keys(\old(list)) == lsegk(\old(list), NULL)) // this needs to be proved !!

		_(assert \lsegStar(new_list, last))
		_(assert \lsegStar(\old(list), list))
		_(assert \subset(N(new_list), G1))
		while(list != NULL)
			//_(invariant \disjoint(N(list), N(new_list)))
			_(invariant \sllStar(\old(list), new_list))
			_(invariant \sllStar(list, new_list))
			_(invariant \lsegStar(\old(list), list)) // (lseg-star-old-list-list)
			_(invariant \lsegStar(new_list, last))
			_(invariant \disjoint(N(list), N(last)))
			_(invariant \disjoint(N(\old(list)), N(last))) // disj-old-list-last
			_(invariant last->next == NULL)
			_(invariant \subset(N(\old(list)), G1)) // (subs-old-list-G1)
			_(invariant \subset(N(list), G1)) // [] shows (lseg-star-new-list)
			_(invariant \subset(N(new_list), G1))
			_(invariant \subset(N(list), N(\old(list))))
			_(invariant \subset(N(last), N(new_list)))
			_(invariant \subset(lsegN(\old(list), list), N(\old(list)))) // [KEY] shows (lseg-star-old-list-list)
			//_(invariant \subset(lsegN(new_list, last), N(new_list)))   // this form of the invariant corresponds to the [KEY] inv, only for the list segment from the new_list to last
			//_(invariant \subset(N(last), N(new_list)))
			_(invariant keys(new_list) == lsegk(\old(list), list)) // [KEY] shows (POST-KEYS)
			_(invariant sll(\old(list)))
			_(invariant sll(last))
			_(invariant sll(list))
			_(invariant mutable_list(list))
			_(invariant last != NULL && mutable_list(last))
		{
			_(assume unfoldAll(list))

			_(ghost \state S3 = \now())
			Node * tail = (Node *)malloc(sizeof(Node));
			_(assume tail != NULL)
			_(assume !(tail \in G1))
			_(ghost G1 = G1 \union {tail})

			// locs: \old(list), list, new_list, last, tail
			tail->key = list->key;
			tail->next = NULL;
			_(assume unfoldAll(tail))
			_(ghost \state S4 = \now())
			_(assume maintainsAcross(tail, \old(list), S3, S4)) // shows (subs-old-list-G1)
			_(assume maintainsAcross(tail, list, S3, S4))
			_(assume maintainsAcross(tail, last, S3, S4))
			_(assume maintainsAcross(tail, new_list, S3, S4))
			_(assume maintainsAcrossLseg(tail, \old(list), list, S3, S4))
			_(assume maintainsAcrossLseg(tail, new_list, last, S3, S4))


			_(assert sll(tail) && sll(list))
			_(assert sll(\old(list)))
			_(assert \lsegStar(new_list, last))
			_(assert \subset(N(\old(list)), G1))
			_(assert \lsegStar(\old(list), list))

			last->next = tail;
			_(assume unfoldAll(last))
			_(ghost \state S5 = \now())
			_(assume maintainsAcross(last, tail, S4, S5))
			_(assume maintainsAcrossLseg(tail, \old(list), last, S4, S5))
			_(assume maintainsAcross(last, \old(list), S4, S5))
			_(assume maintainsAcross(last, list, S4, S5))
			_(assume maintainsAcross(last, new_list, S4, S5))
			_(assume maintainsAcrossLseg(last, new_list, last, S4, S5))
			_(assume maintainsAcrossLseg(last, \old(list), list, S4, S5))

			_(assert sll(tail) && sll(last))
			//_(assert sll(\old(list)) && sll(list))
//			_(assert sll(new_list))
			_(assert \lsegStar(new_list, last))
			_(assert \subset(N(new_list), G1))
			_(assert \lsegStar(\old(list), list))
			_(assert \subset(N(\old(list)), G1)) // follows form disj-old-list-last
			
			_(assume unfoldAll(last))
			last = last->next;
			_(ghost \state S6 = \now())
			_(assert sll(last))
			_(assert N(last) == {tail})
			_(assert !(tail \in lsegN(new_list, last)))
			//_(assert N(new_list) == lsegN(new_list, last) \union \at(S5, N(last)))
			_(assert !(tail \in lsegN(new_list, last)))

			_(assume unfoldAll(list))
			_(assume unfoldMutable(list))
			_(assume unfoldAllLseg(list, list->next))
			list = list->next;

			_(assert \lsegStar(\old(list), list))
			_(assert sll(list))
		}
		_(assert last->next == NULL)
		_(assert sll(list))
		//_(assert keys(new_list) == lsegk(\old(list), list))
		//_(assert lsegk(\old(list), NULL) == keys(\old(list)))
		//_(assert keys(new_list) == keys(\old(list)))
	}
	
	return new_list;
}

Node * g_slist_reverse(Node * list)
	_(requires sll(list))
	_(ensures sll(\result))
	_(ensures keys(\result) == \old(keys(list)))
{
	_(assume mutable_list(list))
	Node * prev = NULL;
	while(list != NULL) 
		_(invariant \sllStar(list, prev))
		_(invariant mutable_list(list))
		_(invariant \intset_union(keys(list), keys(prev)) == \old(keys(list)))
	{
		_(assume unfoldAll(list))
		_(assume unfoldMutable(list))
		_(ghost \state S1 = \now())

		Node * next = list->next;
		_(assert sll(list) && sll(next) && sll(prev))
		_(ghost \state S2 = \now())

		// list, prev, next
		list->next = prev;
		_(assume unfoldAll(list))
		_(ghost \state S3 = \now())
		_(assume maintainsAcross(list, prev, S2, S3))
		_(assume maintainsAcross(list, next, S2, S3))

		_(assert sll(list) && sll(prev))

		prev = list;
		list = next;
		_(assert sll(list))
	}
	return prev;
}

Node * g_slist_nth(Node * list, int n)
	_(requires sll(list))
	_(requires n >= 0)
	_(ensures sll(list))
	_(ensures sll(\result))
	_(ensures \result == NULL ==> ((\natural) n >= llen(list)))
	_(ensures \result != NULL ==> ((llen(list) - llen(\result)) == (\natural) n))
	_(ensures \result != NULL ==> (lseglen(list, \result) == (\natural) n))
	_(ensures \lsegStar(list, \result))
{
	_(assume mutable_list(list))
	while(n > 0 && list != NULL)
		_(invariant sll(list))
		_(invariant \lsegStar(\old(list), list))
		_(invariant mutable_list(list))
		_(invariant n >= 0)
		_(invariant list == NULL ==> ((\natural) \old(n) >= llen(\old(list))))
		_(invariant list != NULL ==> ((\natural)(\old(n) - n) == (llen(\old(list)) - llen(list))))
		_(invariant llen(\old(list)) == (lseglen(\old(list), list) + llen(list)) )
		_(invariant list != NULL ==> (lseglen(\old(list), list) == (\natural) (\old(n) - n)))
		//_(invariant )
	{
		_(assume unfoldMutable(list))
		_(assume unfoldAll(list))
		_(assert n > 0)
		n--;
		_(assume unfoldAll(list))
		_(assume unfoldAllLseg(list, list->next))
		list = list->next; // special case: unfold list segment, use \old(list) as a location, use lemma skip for \old(list) to list
		_(ghost LemmaSkip(\old(list), list))
	}
	_(assert list != NULL ==> n == 0)
	_(assert list != NULL ==> (llen(\old(list)) - llen(list)) == (\natural) \old(n))
	_(assert list != NULL ==> (lseglen(\old(list), list) == (\natural) \old(n)))
	//_(assert list == \old(list) ==> n <= 0)
	return list;
}


// do not like the approach with the ghost out parameter
int g_slist_nth_data(Node * list, int n _(out Node * ret_list))
	_(requires sll(list))
	_(requires n >= 0)
	_(ensures sll(list))
	_(ensures sll(ret_list))
	_(ensures \lsegStar(list, ret_list))
	_(ensures (\natural)n >= llen(list) ==> \result == -1)
	_(ensures ret_list != NULL ==> \result == ret_list->key)
	_(ensures ret_list != NULL ==> (lseglen(list, ret_list) == (\natural)n))
{
	_(ghost ret_list = list ;)
	_(assume mutable_list(list))
	int res;
	while(n > 0 && list != NULL)
		_(invariant sll(list))
		_(invariant sll(ret_list))
		_(invariant \lsegStar(\old(list), list))
		_(invariant mutable_list(list))
		_(invariant n >= 0)
		_(invariant list == NULL ==> (\natural) \old(n) >= llen(\old(list)))
		_(invariant list != NULL ==> (llen(\old(list)) - llen(list)) == (\natural) (\old(n) - n))
		_(invariant list != NULL ==> (lseglen(\old(list), list) == (\natural) (\old(n) - n)))
		_(invariant ret_list == list)
	{
		_(assume unfoldMutable(list))
		_(assume unfoldAll(list))
		n--;
		_(assume unfoldAll(list))
		_(assume unfoldAllLseg(list, list->next))
		list = list->next;
		_(ghost ret_list = list ;)
		_(ghost LemmaSkip(\old(list), list))
	}
	_(assert ret_list != NULL ==> (lseglen(\old(list), ret_list)) == (\natural) (\old(n)))
	if (list != NULL) {
		res = list->key;
	} else {
		res = -1;
	}
	_(assert ret_list != NULL ==> (lseglen(\old(list), list) == (\natural)(\old(n))))
	_(assert ret_list != NULL ==> res == list->key)
	return res;
}


Node * g_slist_find(Node * list, int data)
	_(requires sll(list))
	_(ensures  sll(\result))
	_(ensures \lsegStar(list, \result))
	_(ensures \result == NULL || \result->key == data)
{
	_(assume mutable_list(list))
	while(list != NULL)
		_(invariant sll(list))
		_(invariant \lsegStar(\old(list), list))
		_(invariant mutable_list(list))
	{
		_(assume unfoldMutable(list))
		_(assume unfoldAll(list))
		if (list->key == data) {
			break;
		}
		_(assume unfoldAll(list))
		_(assume unfoldAllLseg(list, list->next))
		list = list->next;
		_(ghost LemmaSkip(\old(list), list))

	}
	return list;
}

int g_slist_position(Node * list, Node * link)
	_(requires sll(list))
	_(requires llen(list) < INT_MAX)
	_(ensures sll(list))
	_(ensures \result == -1 ==> !(link \in N(list)))
	_(ensures (link \in N(list)) ==> \result >= 0)
	_(ensures \result >= 0 ==> \lsegStar(list, link))
	_(ensures \result >= 0 ==> lseglen(list, link) == (\natural)\result)
{
	_(assume mutable_list(list))
	int i;

	i = 0;
	while(list != NULL)
		_(invariant sll(list))
		_(invariant \lsegStar(\old(list), list))
		_(invariant !(link \in lsegN(\old(list), list)))
		_(invariant mutable_list(list))
		_(invariant llen(\old(list)) - llen(list) == (\natural)i)
		_(invariant lseglen(\old(list), list) == (\natural) i)
		_(invariant i < INT_MAX)
		_(invariant i >= 0)
	{
		_(assume unfoldMutable(list))
		_(assume unfoldAll(list))

		if (list == link) {
			
			return i;
		}
		i ++;
		_(assume unfoldAll(list))
		list = list->next;
		_(ghost LemmaSkip(\old(list), list))
	}
	return -1;
}

int g_slist_index(Node * list, int data _(out Node *ret_list))
	_(requires sll(list))
	_(requires llen(list) < INT_MAX)
	_(ensures sll(list))
	_(ensures \intset_in(data, keys(list)) <==> \result >= 0)
	_(ensures !\intset_in(data, keys(list)) <==> \result == -1)
	_(ensures \lsegStar(list, ret_list))
	_(ensures ret_list != NULL ==> lseglen(list, ret_list) == (\natural) \result)
	_(ensures ret_list != NULL ==> ret_list->key == data)
{
	_(assume mutable_list(list))
	_(ghost ret_list = list ;)
	int i; 

	i = 0;
	while(list != NULL)
		_(invariant sll(list))
		_(invariant sll(\old(list)))
		_(invariant \lsegStar(\old(list), list))
		_(invariant llen(\old(list)) - llen(list) == (\natural) i)
		_(invariant !\intset_in(data, lsegk(\old(list), list)))
		_(invariant lseglen(\old(list), list) == (\natural) i)
		_(invariant i < INT_MAX)
		_(invariant i >= 0)
		_(invariant mutable_list(list))
		_(invariant ret_list == list)
	{
		_(assume unfoldMutable(list))
		_(assume unfoldAll(list))
		if(list->key == data) {
			return i;
		}
		i ++;
		_(assume unfoldAll(list))
		_(assume unfoldAllLseg(list, list->next))
		list = list->next;
		_(ghost ret_list = list ;)
		_(ghost LemmaSkip(\old(list), list))
	}
	_(assert !\intset_in(data, keys(\old(list))))
	return -1;
}

uint g_slist_length(Node * list)
	_(requires sll(list))
	_(requires llen(list) < UINT_MAX)
	_(ensures  sll(list))
	_(ensures \result == llen(list))
{
	_(assume mutable_list(list))
	uint length;

	length = 0;
	while(list != NULL)
		_(invariant sll(list))
		_(invariant sll(\old(list)))
		_(invariant \lsegStar(\old(list), list))
		_(invariant llen(\old(list)) - llen(list) == (\natural) length) // (llen-old-cur-len)
		_(invariant length < UINT_MAX) // (len-lt-umax)
		_(invariant mutable_list(list))
	{
		_(assume unfoldMutable(list))
		_(assume unfoldAll(list))
		length++; // (len-lt-max) and (llen-old-cur-len) show [length++] does not overflow
		_(assume unfoldAll(list))
		list = list->next;
		_(ghost LemmaSkip(\old(list), list))
	}
	return length;
}


Node * g_slist_insert_sorted(Node * list, int data)
	_(requires srtl(list))
	_(ensures  srtl(\result))
	_(ensures  keys(\result) == \intset_union(\old(keys(list)), \intset_singleton(data)))
{
	// list is implicitly the head of the list
	_(ghost \objset G0 = N(list) ;)
	_(assume mutable_list(list))
	Node * tmp_list = list;
	Node * prev_list = NULL;
	Node * new_list = NULL;
	// locs: list, tmp_list, prev_list, new_list

	if (list == NULL) {
		new_list = (Node *) malloc(sizeof(Node));
		_(assume new_list != NULL)
		_(assume !(new_list \in G0))
		new_list->key = data;
		new_list->next = NULL;
		_(assume unfoldAllSort(new_list))
		_(assert srtl(new_list))
		_(assert keys(new_list) == \intset_union(keys(list), \intset_singleton(data)))
		return new_list;
	}

	_(assert tmp_list != NULL)
	// TODO: minor modification is to use cmp function for comparison
	// (one could also argue that cmp function is not necessary in this example,
	// since it does not bring any new information)
	while(tmp_list->next != NULL && tmp_list->key < data) 
		_(invariant \subset(N(tmp_list), G0))
		_(invariant \subset(N(prev_list), G0))
		_(invariant \subset(lsegN(list, tmp_list), G0))
		_(invariant \subset(lsegN(list, prev_list), G0))
		_(invariant srtl(list))
		_(invariant srtl(prev_list))
		_(invariant srtl(tmp_list))
		_(invariant \srtlsegStar(list, tmp_list))
		_(invariant \srtlsegStar(list, prev_list))
		_(invariant prev_list == NULL ==> tmp_list == list)
		_(invariant prev_list != NULL ==> prev_list->next == tmp_list)
		_(invariant prev_list != NULL ==> \intset_ge(data, lsegk(list, prev_list)))
		_(invariant prev_list != NULL ==> \intset_ge(data, lsegk(list, tmp_list)))
		_(invariant prev_list != NULL ==> data >= prev_list->key)
		_(invariant mutable_list(prev_list))
		_(invariant tmp_list != NULL && mutable_list(tmp_list))
	{
		_(assume unfoldMutable(tmp_list))
		_(assume unfoldAllSort(tmp_list))
		prev_list = tmp_list;
		_(assume unfoldAllSort(tmp_list))
		tmp_list = tmp_list->next;
	}
	_(assert prev_list == NULL ==> tmp_list == list)
	_(assert tmp_list->next == NULL || data <= tmp_list->key)
	_(assert prev_list != NULL ==> prev_list->next == tmp_list)
	_(assert srtl(list) && srtl(tmp_list) && srtl(prev_list))
	_(assert \srtlsegStar(list, tmp_list) && \srtlsegStar(list, prev_list))
	_(ghost \state S2 = \now())

	// locs: list, tmp_list, prev_list, new_list
	new_list = (Node *) malloc(sizeof(Node));
	_(assume new_list != NULL)
	_(assume !(new_list \in G0))
	new_list->key = data;
	_(ghost \state S3 = \now())
	_(assume unfoldAllSort(new_list))
	// REPEATING: maintaining recursive funcs/preds across the modified locations
	_(assume maintainsAcrossSort(new_list, list, S2, S3))
	_(assume maintainsAcrossSort(new_list, tmp_list, S2, S3))
	_(assume maintainsAcrossSort(new_list, prev_list, S2, S3))
	_(assume maintainsAcrossSrtlseg(new_list, list, tmp_list, S2, S3))
	_(assume maintainsAcrossSrtlseg(new_list, list, prev_list, S2, S3))

	// -------------- verification "environment" ----------------------------
	_(assert tmp_list->next == NULL || data <= tmp_list->key)
	_(assert srtl(list) && srtl(tmp_list) && srtl(prev_list))
	_(assert \srtlsegStar(list, tmp_list) && \srtlsegStar(list, prev_list))	
	// -----------------------------------------------------------------------
	// locs: list, tmp_list, prev_list, new_list
	if (tmp_list->next == NULL && data >= tmp_list->key) { // adding to the tail of the list
		_(assume unfoldAllSort(tmp_list)) // shows (intset-ge-data-keys-tmp_list)
		//_(assert \intset_ge(data, keys(tmp_list))) // (intset-ge-data-keys-tmp_list)
		_(ghost \state S3a = \now())
		tmp_list->next = new_list;
		_(assume unfoldAllSort(tmp_list))
		_(ghost \state S3b = \now())
		_(assume maintainsAcrossSort(tmp_list, new_list, S3a, S3b))
		_(assume maintainsAcrossSrtlseg(new_list, list, tmp_list, S3a, S3b))
		_(assume maintainsAcrossSort(tmp_list, list, S3a, S3b))
		_(assume maintainsAcrossSort(tmp_list, prev_list, S3a, S3b))
		_(assume maintainsAcrossSort(tmp_list, new_list, S3a, S3b))
		_(assume maintainsAcrossSrtlseg(tmp_list, list, tmp_list, S3a, S3b))

		new_list->next = NULL;
		_(assume unfoldAllSort(new_list))
		_(ghost \state S4 = \now())
		// maintaining across all locs
		_(assume maintainsAcrossSort(new_list, list, S3b, S4))
		_(assume maintainsAcrossSort(new_list, tmp_list, S3b, S4))
		_(assume maintainsAcrossSort(new_list, prev_list, S3b, S4))
		// maintainting across all lsegs
		_(assume maintainsAcrossSrtlseg(new_list, list, tmp_list, S3b, S4))
		_(assume maintainsAcrossSrtlseg(new_list, list, prev_list, S3b, S4))
		//_(ghost LemmaSkipSort(tmp_list, new_list))
		_(assert srtl(new_list))
		_(assert srtl(list))
		_(assert keys(list) == \intset_union(\old(keys(list)), \intset_singleton(data)))
		return list;
	}

	// -------------- verification "environment" ----------------------------
	_(assert tmp_list->next == NULL || data <= tmp_list->key)
	_(assert srtl(list) && srtl(tmp_list) && srtl(prev_list))
	_(assert \srtlsegStar(list, tmp_list) && \srtlsegStar(list, prev_list))	

	// -----------------------------------------------------------------------
	//_(ghost \state S5 = \now())
	if (prev_list != NULL) {
		_(assume unfoldAllSort(prev_list)) // (unfold-all-sort-prev-list) shows (list-in-N-prev-list) 
		_(assume unfoldAllSort(tmp_list))
		// --------------------------------------------------------------------------
		// this is not in the original code, but it is necessary for re-establishing
		// of list being a sorted singly-linked list
		_(ghost \state S5a = \now())
		new_list->next = NULL;
		_(assume unfoldAllSort(new_list))
		_(ghost \state S5b = \now())
		_(assume maintainsAcrossSort(new_list, list, S5a, S5b))
		_(assume maintainsAcrossSort(new_list, tmp_list, S5a, S5b))
		_(assume maintainsAcrossSort(new_list, prev_list, S5a, S5b))
		_(assume maintainsAcrossSrtlseg(new_list, list, tmp_list, S5a, S5b))
		_(assume maintainsAcrossSrtlseg(new_list, list, prev_list, S5a, S5b))
		// -------------------------------------------------------------------------

		_(assert data >= prev_list->key)
		_(ghost \state S6 = \now())
		prev_list->next = new_list;
		_(assume unfoldAllSort(prev_list))
		_(ghost \state S7 = \now())
		_(assume maintainsAcrossSort(prev_list, new_list, S6, S7)) // prev_list is disjoint from the new_list
		_(assume maintainsAcrossSrtlseg(new_list, list, prev_list, S6, S7)) // assignment does not introduce cycles
		_(assume maintainsAcrossSort(prev_list, list,     S6, S7))
		_(assume maintainsAcrossSort(prev_list, tmp_list, S6, S7)) // tmp_list is after prev_list, so this is fine
		//_(assume maintainsAcrossSrtlseg(new_list, list, tmp_list, S6, S7)) // this introduces unsoundness because the assignments _is_ betweem list and tmp_list, since tmp_list comes after prev_list
		                                                                     // the fact that new_list is not in lsegN(list, temp_list) does not mean it is preserved!!!
		// BEWARE: thinking about the list segments - maintaining across list segment _only_ for the modified locations
		_(assume maintainsAcrossSrtlseg(prev_list, list, prev_list, S6, S7)) 
		_(assume maintainsAcrossSrtlseg(prev_list, list, tmp_list, S6, S7)) 
		_(assert srtl(new_list))
		_(assert !(prev_list \in N(new_list)))
		_(assert \intset_le(prev_list->key, keys(new_list)))
		_(assert srtl(prev_list))
		_(ghost LemmaSkipSort(list, prev_list) ;)

		new_list->next = tmp_list;
		_(assume unfoldAllSort(new_list))
		_(ghost \state S8 = \now() ;)
		_(assume maintainsAcrossSort(new_list, tmp_list, S7, S8))
		_(assume maintainsAcrossSrtlseg(tmp_list, list, new_list, S7, S8)) // this one is _crucial_ (otherwise, unfolding of tmp_list is needed)

		_(assume maintainsAcrossSort(new_list, list, S7, S8))
		_(assume maintainsAcrossSort(new_list, prev_list, S7, S8))
		_(assume maintainsAcrossSrtlseg(new_list, list, prev_list, S7, S8))
		_(assume maintainsAcrossSrtlseg(new_list, list, tmp_list, S7, S8))
		//_(assert srtl(tmp_list))
		//_(assert !(new_list \in N(tmp_list)))
		//_(assert srtl(new_list))
		//_(ghost LemmaSkipSort(list, new_list))

		_(assert srtl(list))
		_(assert keys(list) == \intset_union(\old(keys(list)), \intset_singleton(data)))
		return list;
	} else { // adding to the head of the list
		_(ghost \state S5a = \now())
		_(assume unfoldAllSort(list)) // (unfold-all-sort-list) shows (intset-le-data-keys-list)
		//_(assert \intset_le(data, keys(list))) // (intset-le-data-keys-list)
		new_list->next = list;
		_(assume unfoldAllSort(new_list))
		_(ghost \state S6 = \now())
		_(assume maintainsAcrossSort(new_list, list, S5a, S6))
		
		_(assert keys(new_list) == \intset_union(\old(keys(list)), \intset_singleton(data)))
		return new_list;
	}
}	

Node * g_slist_sort_merge(Node * l1, Node * l2)
	_(requires \srtlStar(l1, l2))
	_(ensures srtl(\result))
	_(ensures keys(\result) == \intset_union(\old(keys(l1)), \old(keys(l2))))
	_(ensures N(\result) == (\old(N(l1)) \union \old(N(l2))))
{
	_(ghost \intset k1 = keys(l1) ;)
	_(ghost \intset k2 = keys(l2) ;)
	_(ghost \intset init_keys = \intset_union(keys(l1), keys(l2)) ;)
	_(assert \srtlStar(l1, l2))
	_(ghost \objset G0 = N(l1) \union N(l2) ;)
	_(ghost \state S0 = \now() ;)
	Node * list, * l;
	_(assume mutable_list(l1) && mutable_list(l2))
	//_(assume mutable_list(l))

	// l = &list; // this invalidates \srtlStar at the function entry
	// locs: l1, l2, list
	list = (Node *) malloc(sizeof(Node));
	_(assume list != NULL)
	_(assume !(list \in G0))
	_(ghost \state S1 = \now() ;)
	_(assume maintainsAcrossSort(list, l1, S0, S1))
	_(assume maintainsAcrossSort(list, l2, S0, S1))


	// list head is a (sort of) sentinel node
	// it can be also thought as bottom (in this case -inf)
	list->key = INT_MIN; 
	list->next = NULL; 
	_(assume unfoldAllSort(list))
	_(ghost \state S2 = \now() ;)
	_(assume maintainsAcrossSort(list, l1, S1, S2))
	_(assume maintainsAcrossSort(list, l2, S1, S2))

	l = list;
	
	// ----------- venv -------------
	_(assert \srtlStar(l1, l2))
	_(assert \srtlStar(l, l1))
	_(assert \srtlStar(l, l2))
	// ------------------------------
	
	_(assert init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
	_(assert \intset_union(k1, k2) == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))

	while(l1 != NULL && l2 != NULL)
		//_(invariant keys(list) == \intset_union(\old(keys(l1)), 
		_(invariant \intset_le(l->key, keys(l1)))
		_(invariant \intset_le(l->key, keys(l2)))
		_(invariant \srtlStar(l, l1))
		_(invariant \srtlStar(l, l2))
		_(invariant \srtlStar(l1, l2))
		_(invariant \srtlsegStar(list, l)) // (inv-strlseg-star-list-l) follows from (inv-disj-N-l1-lsegN-list-l) and (inv-disj-N-l2-lsegN-list-l)
		_(invariant list->next != NULL ==> \srtlsegStar(list->next, l)) // (inv-strlseg-star-list-l) follows from (inv-disj-N-l1-lsegN-list-l) and (inv-disj-N-l2-lsegN-list-l)
		_(invariant srtl(list))
		_(invariant srtl(list->next))
		_(invariant list->next == NULL ==> l == list)
		_(invariant init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2)))) // this is a workaround for the invariant below
		_(invariant G0 == (N(list->next) \union N(l1) \union N(l2)))
		//_(invariant \intset_union(k1, k2) == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2)))) // this does not work, see above for a workaround
		//_(invariant \intset_union(k1, k2) == init_keys)
		_(invariant \disjoint(N(l1), lsegN(list, l))) // (inv-disj-N-l1-lsegN-list-l) shows (inv-strlseg-star-list-l)
		_(invariant \disjoint(N(l2), lsegN(list, l))) // (inv-disj-N-l2-lsegN-list-l) shows (inv-strlseg-star-list-l)
		_(invariant l->next == NULL)
		_(invariant l != NULL)
		_(invariant mutable_list(l))
		_(invariant mutable_list(l1))
		_(invariant mutable_list(l2))
	{
		_(assume unfoldAllSort(l1))
		_(assume unfoldAllSort(l2))
		//_(assert keys(list) == \intset_union(keys(list->next), \intset_singleton(INT_MIN)))
		//_(assert \intset_union(k1, k2) == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2)))) // see below for a workaround
		_(assert init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
		_(assume unfoldMutable(l))
		if (l1->key <= l2->key)
		{
			_(assume unfoldAllSort(l1))
			_(assume unfoldAllSort(l2))
			//_(assert \disjoint(N(l1), lsegN(list, l))) // TODO: connect to the corresponding invariants
			_(ghost \state S5 = \now())
			l->next = l1;
			_(assume unfoldAllSort(l))
			_(assume unfoldAllSrtlseg(list, l)) // [crucial] (because of the \srtlsegStar(list, l) loop inv)
			_(ghost \state S6 = \now())
			_(assume maintainsAcrossSort(l, l1, S5, S6))
			_(assume maintainsAcrossSort(l, l2, S5, S6))
			_(assume maintainsAcrossSrtlseg(l, list, l, S5, S6))
			_(assume maintainsAcrossSrtlseg(l, list->next, l, S5, S6)) // [crucial] (because of the list->next != NULL ==> \srtlsegStar(list->next, l) loop inv)
			_(assert \intset_le(l->key, keys(l1)))
			
			//_(assert \srtlsegStar(list->next, l))
			_(assert \srtlStar(l1, l2))
			_(assert init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
			_(assert \intset_in(l1->key, keys(list->next)))

			_(assume unfoldMutable(l1))
			_(assume unfoldAllSort(l1))
			l1 = l1->next;
			_(ghost \state S7 = \now())
			//_(assume unfoldAllSort(list))
			//_(assert \srtlsegStar(list, l))
			_(assert \srtlStar(l1, l2))
			_(assert \intset_le(l->key, keys(l1)))
			//_(assert \intset_union(k1, k2) == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
			_(assert init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
		} else {
			_(assume unfoldAllSort(l1))
			_(assume unfoldAllSort(l2))
			_(ghost \state S5 = \now())
			//_(assert \disjoint(N(l2), lsegN(list, l)))
			l->next = l2;
			_(assume unfoldAllSort(l))
			_(assume unfoldAllSrtlseg(list, l)) // [crucial] (because of the \srtlsegStar(list, l) loop inv)
			_(ghost \state S6 = \now())
			_(assume maintainsAcrossSort(l, l2, S5, S6))
			_(assume maintainsAcrossSort(l, l1, S5, S6))
			_(assume maintainsAcrossSrtlseg(l, list, l, S5, S6))
			_(assume maintainsAcrossSrtlseg(l, list->next, l, S5, S6)) // [crucial] (because of the list->next != NULL ==> \srtlsegStar(list->next, l) loop inv)

			//_(assert \intset_in(l2->key, keys(list->next)))
			_(assert srtl(l->next))
			_(assert \srtlStar(l1, l2))
			_(assert \disjoint(lsegN(list, l), N(l)))
			_(assert \srtlsegStar(list, l))

			_(assume unfoldMutable(l2))
			_(assume unfoldAllSort(l2))
			l2 = l2->next;
			_(ghost \state S7 = \now())

			_(assert \srtlStar(l1, l2))
			_(assert \intset_le(l->key, keys(l1)))
			_(assert init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
		}
		_(ghost \state S8 = \now())
		_(assert \intset_le(l->key, keys(l1)))
		_(assert init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
		
		//_(assert \srtlsegStar(list, l))
		_(assert \srtlStar(l1, l2))
		_(assume unfoldAllSort(l))
		l = l->next;
		_(ghost \state S9 = \now())
//		_(assert \intset_le(l->key, keys(l1)))
//		_(assert \intset_le(l->key, keys(l2)))
//		_(assert init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2)))

		l->next = NULL;
		_(assume unfoldAllSort(l))
		_(ghost \state S10 = \now())
		_(assume maintainsAcrossSort(l, l1, S9, S10))
		_(assume maintainsAcrossSort(l, l2, S9, S10))
		_(assume maintainsAcrossSrtlseg(l, list, l, S9, S10))
		_(assume maintainsAcrossSrtlseg(l, list->next, l, S9, S10))
		_(assert \srtlStar(l1, l2))
		_(assert \srtlsegStar(list, l))

		//_(assert \intset_union(k1, k2) == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
		_(assert init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
	}
	_(assert list->next == NULL ==> l == list)
	_(assert init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
	_(assert G0 == (N(list->next) \union N(l1) \union N(l2)))
	//_(assert \false)
	//_(assert list->next == NULL)
	//_(assert \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))) == \intset_union(\old(keys(l1)), \old(keys(l2))))

	_(ghost \state S11 = \now())
	_(assert \srtlStar(l1, l2))
	_(assert \srtlStar(l, l1))
	_(assert \srtlStar(l, l2))
	_(assert srtl(l))
	_(assert \srtlsegStar(list, l))
	_(assert \intset_le(l->key, keys(l1)) || \intset_le(l->key, keys(l2)))
	_(assert init_keys == \intset_union(keys(list->next), \intset_union(keys(l1), keys(l2))))
	if (l1 != NULL) {
		_(assert l2 == NULL)
		_(assert init_keys == \intset_union(keys(list->next), keys(l1)))
		_(assert keys(list->next) == \intset_union(lsegk(list->next, l), keys(l)))
		_(assert G0 == (N(list->next) \union N(l1)))
		_(assert srtl(list->next))
		l->next = l1;
		_(assume unfoldAllSort(l))
		_(assume unfoldAllSrtlseg(list, l))
		_(ghost \state S12 = \now())
		_(assume maintainsAcrossSort(l, l1, S11, S12))
		_(assume maintainsAcrossSrtlseg(l, list, l, S11, S12))
		_(assume maintainsAcrossSrtlseg(l, list->next, l, S11, S12))
		_(ghost LemmaSkipSort(list->next, l))
		//_(assert srtl(l1))
		//_(assert srtl(l->next))
		//_(assert !(l \in N(l->next)))
		//_(assert \intset_le(l->key, keys(l1)))
		_(assert srtl(l))
		_(assert srtl(list))
		_(assert srtl(list->next))
		_(assert \srtlsegStar(list, l))
		_(assert keys(l) == \intset_union(keys(l1), \intset_singleton(l->key)))
		_(assert keys(list->next) == \intset_union(lsegk(list->next, l), keys(l)))
		_(assert init_keys == keys(list->next))
		_(assert N(list->next) == lsegN(list->next, l) \union N(l))
		_(assert G0 == N(list->next))
	} else {
		_(assert l1 == NULL)
		_(assert G0 == (N(list->next) \union N(l2)))
		l->next = l2;
		_(assume unfoldAllSort(l))
		_(assume unfoldAllSrtlseg(list, l))

		_(ghost \state S12 = \now())
		_(assume maintainsAcrossSort(l, l2, S11, S12))
		_(assume maintainsAcrossSrtlseg(l, list, l, S11, S12))
		_(assume maintainsAcrossSrtlseg(l, list->next, l, S11, S12))
		_(ghost LemmaSkipSort(list->next, l))
		_(assert srtl(l))
		_(assert srtl(list))
		_(assert \srtlsegStar(list, l))
		_(assert init_keys == keys(list->next))
		_(assert N(list->next) == lsegN(list->next, l) \union N(l))
	}
	_(assert srtl(list))
	_(assert srtl(list->next))
	_(assert \old(keys(l1)) == k1)
	_(assert \old(keys(l2)) == k2)
	_(assert keys(list->next) == \intset_union(\old(keys(l1)), \old(keys(l2))))
	_(assert G0 == N(list->next))
	return list->next;
}
/*

Node * g_slist_sort_merge(Node * l1, Node * l2)
	_(requires \srtlStar(l1, l2))
	_(ensures srtl(\result))
	_(ensures keys(\result) == \intset_union(\old(keys(l1)), \old(keys(l2))))
	_(ensures keys(\result) == \intset_union(keys(l1), keys(l2)))
	_(ensures N(\result) == (\old(N(l1)) \union \old(N(l2))))
	;

Node * g_slist_sort_real(Node * list)
	_(requires sll(list))
	_(ensures srtl(\result))
	_(ensures keys(\result) == \old(keys(list)))
{
	_(ghost \objset G0 = N(list))
	Node * l1, * l2;
	_(assume mutable_list(list))
	// locs: list, l1, l2

	if (list == NULL) {
		return list;
	}

	if (list->next == NULL) {
		_(assume unfoldAllSort(list))
		return list;
	}

	// locs: list, l1, l2
	l1 = list;
	_(assert sll(l1))
	_(assert \lsegStar(list, l1))
	_(assert l1 != NULL)

	_(assume unfoldAll(list))
	l2 = list->next;
	_(assert sll(l2))
	_(assert \lsegStar(list, l2))
	_(assert \lsegStar(l1, l2))
	_(assert l1->next == l2)

	_(assume unfoldMutable(list))
	_(assume unfoldMutable(l2))
	_(assume unfoldAll(l2))
	l2 = l2->next;
	_(assert sll(l2))
	_(assert \lsegStar(list, l2))
	_(assert \lsegStar(l1, l2))
	_(assert l1->next->next == l2)
	
	//_(assert G0 == (lsegN(list, l1) \union lsegN(l1, l2) \union N(l2)))

	_(assume unfoldMutable(l2))
	while(l2 != NULL)
		_(invariant \old(keys(list)) == \intset_union(lsegk(list, l1), \intset_union(lsegk(l1, l2), keys(l2))))
		_(invariant sll(l1))
		_(invariant sll(l2))
		_(invariant \lsegStar(list, l1))
		_(invariant \lsegStar(list, l2))
		_(invariant l1 != NULL)
		_(invariant \lsegStar(l1, l2))
		_(invariant G0 == (lsegN(list, l1) \union lsegN(l1, l2) \union N(l2)))
		_(invariant mutable_list(l2))
		_(invariant mutable_list(l1))
	{
		_(assume unfoldAll(l2))
		_(assume unfoldMutable(l2))
		l2 = l2->next;
		_(assume unfoldMutable(l2))
		if(l2 == NULL) {
			break;
		}
		_(assume unfoldMutable(l1))
		_(assume unfoldAll(l1))
		_(assume unfoldAllLseg(l1, l2)) // [needed to prove \lsegStar(l1, l2)]
		l1 = l1->next;

		_(assume unfoldMutable(l2))
		_(assume unfoldAll(l2))
		l2 = l2->next;
		_(ghost LemmaSkip(list, l1) ;)
		_(ghost LemmaSkip(l1, l2) ;)
		_(ghost LemmaSkip(list, l2) ;)
		//_(assert N(list) == lsegN(list, l1) \union N(l1))
		//_(assert N(l1) == lsegN(l1, l2) \union N(l2))
		//_(assert N(list) == lsegN(list, l2) \union N(l2))
	}
	//_(assert G0 == (lsegN(list, l1) \union lsegN(l1, l2) \union N(l2)))
	_(assume unfoldMutable(l1))
	l2 = l1->next;
	_(assume unfoldAll(l1))
	_(ghost \state S3 = \now())
	_(assert sll(l1))
	_(assert sll(l1->next))
	_(assert sll(l2))
	_(assert \lsegStar(list, l2))
	//_(assert l2 == NULL)
	l1->next = NULL;
	_(assume unfoldAll(l1))
	_(ghost \state S4 = \now())
	_(assume maintainsAcross(l1, l2, S3, S4))
	_(assume maintainsAcrossLseg(l1, list, l2, S3, S4))
	_(assume maintainsAcrossLseg(l1, list, l1, S3, S4))
	//_(assert l2 == NULL)
	_(assert sll(l1))
	_(assert sll(l2))
	_(assert \lsegStar(list, l1))
	_(assert \old(keys(list)) == \intset_union(keys(list), keys(l2)))
	//_(assert G0 == N(list) \union N(l2))
	_(assert \disjoint(N(list), N(l2)))

	_(assert list != NULL)
	// t1 is added to a set of locations
	Node * t1 = g_slist_sort_real(list);
	_(ghost \state S5 = \now())
	_(assume \disjoint(N(t1), (G0 \diff \at(S4, N(list)))))
	_(ghost \objset G1 = N(t1) \union (G0 \diff \at(S4, N(list))))
	_(assume maintainsAcrossSort(list, l1, S4, S5))
	_(assume maintainsAcrossSort(list, l2, S4, S5))
	_(assert \disjoint(N(t1), N(l2)))
	_(assert srtl(t1))
	_(assert sll(l2))

	if (l2 == NULL) {
		return t1;
	}

	//_(assert l2 != NULL)
	// t2 is added to a set of locations
	Node * t2 = g_slist_sort_real(l2);
	_(ghost \state S6 = \now())
	_(assume \disjoint(N(t2), (G1 \diff \at(S5, N(l2)))))
	_(assume maintainsAcrossSort(l2, l1, S5, S6))
	_(assume maintainsAcrossSort(l2, l2, S5, S6))
	_(assume maintainsAcrossSort(l2, t1, S5, S6))
	_(assert srtl(t2))
	_(assert srtl(t1))

	Node * res = g_slist_sort_merge(t1, t2);
	//_(assert \old(keys(t2)) == keys(t2))
	//_(assert \old(keys(list)) == \intset_union(keys(t1), keys(t2)))
	//_(assert keys(res) == \old(keys(list)))
	return res;
}
*/
/*
*/
