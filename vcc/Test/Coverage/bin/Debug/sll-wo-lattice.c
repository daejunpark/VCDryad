
//#include "stdafx.h"
#include <vcc.h>
#include <stdlib.h>


struct node
{
	int key;
	struct node *next;
};


_(def int getKey(struct node * x) {
	return x == NULL ? INT_MAX : x->key;
})

_(def int getMinKey(int x, int y) {
	return y <= x ? y : x;
})

// N is an uninterpreted function, representing the reach set.
// N(NULL) is empty, and root \in N(root) if root is not NULL.
_(abstract \objset N(struct node *root)
	_(reads \universe())
	_(ensures ((root != NULL) ==> (root \in \result))
			&& ((root == NULL) ==> (\result == {})))
	;)

// sll is an uninterpreted function, representing the sorted list.
// sll(NULL) is true.
_(abstract \bool sll(struct node *root)
	_(reads \universe())
	_(ensures (root == NULL) ==> \result)
	;)


// unfold N w.r.t. the location root
_(pure \bool unfoldN(struct node *root)
	_(reads \universe())
	_(ensures \result == (root != NULL ==>
		(N(root) == (N(root->next) \union {root})
		)))
;)

// unfold sll w.r.t. the location root
_(pure \bool unfoldSll(struct node *root)
	_(reads \universe())
	_(ensures \result == (root != NULL ==>
		(sll(root) <==> 
			(sll(root->next) && 
			(! (root \in N(root->next)))) &&
			getKey(root) <= getKey(root->next)
		)))
;)

// unfold minKey w.r.t. the location root
_(pure \bool unfoldMinKey(struct node *root)
	_(reads \universe())
	_(ensures \result == (root != NULL ==>
		getKey(root) == getMinKey(getKey(root), getKey(root->next))
		))
;)


// axioms needed to complete the proof
_(axiom \forall \objset os1, os2; \disjoint(os1, os2) <==> \subset(os1, (\universe() \diff os2)))

_(abstract \bool unfoldAll(\object o)
	_(reads \universe())
	_(ensures unfoldN(o))
	_(ensures unfoldSll(o))
	_(ensures unfoldMinKey(o))
)


_(logic \bool maintainsAcross(struct node * x, struct node * y, \state enter, \state exit) = 
	((! (x \in \at(enter, N(y)))) ==> \at(enter, N(y)) == \at(exit, N(y))) &&
	((! (x \in \at(enter, N(y)))) ==> \at(enter, sll(y)) == \at(exit, sll(y))) &&
	((! (x \in \at(enter, N(y)))) ==> \at(enter, getKey(y)) == \at(exit, getKey(y)))
)

_(logic \bool disjointMaintainsAcross(struct node * x, struct node * y, \state enter, \state exit) =
	(\disjoint(\at(enter, N(x)), \at(enter, N(y))) ==> 
             \at(enter, N(x)) == \at(exit, N(x))) &&
	(\disjoint(\at(enter, N(x)), \at(enter, N(y))) ==> 
             \at(enter, sll(x)) == \at(exit, sll(x))) &&
	(\disjoint(\at(enter, N(x)), \at(enter, N(y))) ==> 
             \at(enter, getKey(x)) == \at(exit, getKey(x))) 

)

struct node * sll_insert(struct node *x, int k)
	_(reads N(x))
	_(requires sll(x))
	_(ensures sll(\result))
	_(ensures getKey(\result) == getMinKey(\old(getKey(x)), k))
{
	// G0 represents the set of locations required at the entry of the function,
	// which should be exactly the heap portion needed by the precondition.
	_(ghost \objset G0 = N(x);)

	_(assume x != NULL ==> \mutable(x) && \writable(x))
	
	if (x == NULL)
	{	
		struct node *leaf = (struct node *) malloc(sizeof(struct node));

		// the global heap is extended with a freshly new address after "malloc"
		_(assert !(leaf \in G0))
		//_(assume ! (leaf \in G0))
		// leaf is correctly allocated
		_(assume leaf != NULL)
		_(ghost \objset G1 = G0 \union {leaf};)
		
		_(ghost \state S1 = \now();)

		// ******************************************
		leaf->key = k;
		leaf->next = NULL;
		// ******************************************
		_(ghost \state S2 = \now();)
		_(assume maintainsAcross(leaf, x, S1, S2))

		// leaf is a new concrete location, unfold all the recursive definitions w.r.t. this location
		_(assume unfoldAll(leaf))

		_(assert G1 == N(leaf))
		// ******************************************
		return leaf;
		// ******************************************
	}
	else if (k > x->key)
	{
		// x is a concrete location at this point, as it has been dereferenced in the conditional
		// unfold all the recursive definitions w.r.t. it.
		_(assume unfoldAll(x))

		// the state at the timestamp 1
		_(ghost \state S1 = \now();)

		// ******************************************
		struct node * temp = sll_insert(x->next, k);
		//*******************************************

		// unfold concrete locations
		_(assume unfoldAll(x))

		// the state at the timestamp 2
		_(ghost \state S2 = \now();)

		// for each symbolic location that is disjoint from the affected portion of the function call (\at(S, N(x->next)),
		// the recursive measures on it are unchanged through the function call.
		// (theoretically, we need to check all locations. If a location is not equal to any concrete location, then it is symbolic.)
		//_(assume disjointMaintainsAcross(x, x->next, S1, S2))
				
		// for each concrete location, its content is unchanged if not affected by the function call
		//_(assume (! (x \in \at(S1, N(x->next)))) ==> (\at(S1, x->key) == \at(S2, x->key) 
		//                                          &&  \at(S1, x->next) == \at(S2, x->next)))

		// the heap portion returned from the function call (temp_2_N) is 
		// disjoint with the heap portion unaffected by the function call.
		_(assume \disjoint(\at(S2, N(temp)), (G0 \diff \at(S1, N(x->next)))))

		// update the heap: remove the heap portion under the function call (N(x->next) at the state S1), 
		// then add the heap portion returned from the function call (N(temp) at the state S2).
		_(ghost \objset G2 = (G0 \diff \at(S1, N(x->next)) \union \at(S2, N(temp))) ;)

		// ******************************************
		x->next = temp;
		// ******************************************

		// unfold concrete locations
		_(assume unfoldAll(x))

		// the state at the timestamp 2
		_(ghost \state S3 = \now();)

		// for each symbolic location that does not reach the modified location (x),
		// the recursive measures on it are unchanged through the function call.
		//_(assume maintainsAcross(x, x->next, S2, S3))		
		_(assume maintainsAcross(x, temp, S2, S3))

		// update the heap
		//_(ghost \objset G3 = G2 ;)

		// check that the heap at the entry of the function is exactly what needed by the postcondition
		_(assert (G2 == N(x)))

		// *****************************************
		_(assert sll(x)) 
		return x;
		// ******************************************
	}
	else
	{
		// unfold concrete locations
		_(assume unfoldAll(x))

		// the state at the timestamp 1
		_(ghost \state S1 = \now();)
		_(assert sll(x->next))
		// ******************************************
		struct node *head = (struct node *) malloc(sizeof(struct node));
		_(assume head != NULL)

		head->key = k;
		head->next = x;
		// ******************************************

		// unfold concrete locations
		_(assume unfoldAll(x))
		_(assume unfoldAll(head))
		// the state at the timestamp 4
		_(ghost \state S4 = \now();)

		// for each symbolic location that does not reach the modified location (head),
		// the recursive measures on it are unchanged through the function call.
		_(assume maintainsAcross(head, x, S1, S4))
		//_(assume maintainsAcross(head, x->next, S1, S4))

		// the global heap is extended with a freshly new address after "malloc"
		_(assume ! (head \in G0))
		_(ghost \objset G4 = G0 \union {head};)

		// check that the heap at the entry of the function is exactly what needed by the postcondition
		_(assert G4 == N(head))

		// ******************************************
		return head;
		// ******************************************
	}
}
