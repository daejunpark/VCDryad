#ifndef DRYAD_BST2SORTED_DEFS_H
#define DRYAD_BST2SORTED_DEFS_H

#include <vcc.h>
#include <stdlib.h>
//#include "intbag_defs.h"
//#include "intset_defs.h"

typedef 
_(dryad "bst:bst_R:bst_keys")
struct b_node {
	struct b_node * left;
	struct b_node * right;
	int key;
} BNode;

typedef 
_(dryad "sortl:sortl_R:sortl_keys")
struct l_node {
	struct l_node * next;
	int key;
} LNode;


// -------------------------- base ------------------------------------------
_(abstract _(dryad "base:bst") \bool bst(struct b_node * root)
	_(reads \universe())
	_(ensures (root == NULL) ==> \result)
;)
_(abstract _(dryad "base:bst_R") \oset bst_reach(struct b_node * root)
	_(reads \universe())
	_(ensures (root != NULL) ==> \oset_in(root, \result))
	_(ensures (root == NULL) ==> (\result == \oset_empty()))
;)
_(abstract _(dryad "base:bst_keys") \intset bst_keys(struct b_node * root)
	_(reads \universe())
	_(ensures root != NULL ==> \intset_in(root->key, \result))
	_(ensures root == NULL ==> (\result == \intset_empty()))
;)

// ---------------------------- unfold --------------------------------------
_(logic _(dryad "unfold:bst") \bool unfold_bst(struct b_node * root) =
	(root != NULL ==>
		(bst(root) <==>
			(bst(root->left) && bst(root->right) 
			&& (! \oset_in(root, \oset_union(bst_reach(root->left), bst_reach(root->right)))) 
			&& !\intset_in(root->key, \intset_union(bst_keys(root->left), bst_keys(root->right)))
			&& \oset_disjoint(bst_reach(root->left), bst_reach(root->right)) 
			&& \intset_disjoint(bst_keys(root->left), bst_keys(root->right))
			&& \intset_lt_one2(bst_keys(root->left), root->key) 
			&& \intset_lt_one1(root->key, bst_keys(root->right)) ) ) )
;)
_(logic _(dryad "unfold:bst_R") \bool unfold_bst_reach(struct b_node * root) =
	(root != NULL ==>
		(bst_reach(root) == \oset_union(\oset_singleton(root), 
                                    \oset_union(bst_reach(root->left), bst_reach(root->right)))))
;)
_(logic _(dryad "unfold:bst_keys") \bool unfold_bst_keys(struct b_node * root) =
	(root != NULL ==>
		(bst_keys(root) == \intset_union(\intset_singleton(root->key), 
										                 \intset_union(bst_keys(root->left),  bst_keys(root->right)))) )
;)
_(logic \bool unfold_bst_all(struct b_node * x) =
	unfold_bst(x)
	&& unfold_bst_reach(x)
	&& unfold_bst_keys(x)
;)

// -------------------------------- same --------------------------------------------------
_(logic _(dryad "same:bst") \bool same_bst(struct b_node * x, \state enter, \state exit) =
	\at(enter, bst(x)) == \at(exit, bst(x))
;)
_(logic _(dryad "same:bst_R")  \bool same_bst_reach(struct b_node * x, \state enter, \state exit) =
	\at(enter, bst_reach(x)) == \at(exit, bst_reach(x))
;)
_(logic _(dryad "same:bst_keys") \bool same_bst_keys(struct b_node * x, \state enter, \state exit) =
	\at(enter, bst_keys(x)) == \at(exit, bst_keys(x))
;)
_(logic \bool same_bst_all(struct b_node * x, \state enter, \state exit) =
	same_bst(x, enter, exit)
	&& same_bst_reach(x, enter, exit)
	&& same_bst_keys(x, enter, exit)
;)

// ----------------------------  cond same  ------------------------------------------------
_(logic _(dryad "cond:bst") \bool cond_same_bst(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y))) ==> \at(enter, bst(y)) == \at(exit, bst(y)))
;)
_(logic _(dryad "cond:bst_R") \bool cond_same_bst_reach(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y))) ==> \at(enter, bst_reach(y)) == \at(exit, bst_reach(y)))
;)
_(logic _(dryad "cond:bst_keys") \bool cond_same_bst_keys(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y))) ==> \at(enter, bst_keys(y)) == \at(exit, bst_keys(y)))
;)
_(logic \bool cond_same_bst_all(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	cond_same_bst(x, y, enter, exit)
	&& cond_same_bst_reach(x, y, enter, exit)
	&& cond_same_bst_keys(x, y, enter, exit)
;)
_(logic _(dryad "cond:sortl") \bool cond_same_sortl(struct b_node * x, struct l_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, sortl_reach(y))) ==> \at(enter, sortl(y)) == \at(exit, sortl(y)))
;)
_(logic _(dryad "cond:sortl_R") \bool cond_same_sortl_reach(struct b_node * x, struct l_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, sortl_reach(y))) ==> \at(enter, sortl_reach(y)) == \at(exit, sortl_reach(y)))
;)
_(logic _(dryad "cond:sortl_keys") \bool cond_same_sortl_keys(struct b_node * x, struct l_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, sortl_reach(y))) ==> \at(enter, sortl_keys(y)) == \at(exit, sortl_keys(y)))
;)
_(logic \bool cond_same_sortl_all(struct b_node * x, struct l_node * y, \state enter, \state exit) =
	cond_same_sortl(x, y, enter, exit)
	&& cond_same_sortl_reach(x, y, enter, exit)
	&& cond_same_sortl_keys(x, y, enter, exit)
;)

// ----------------------------  disj same  ------------------------------------------------
_(logic _(dryad "disj:bst") \bool disj_same_bst(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, bst_reach(y))) ==> \at(enter, bst(y)) == \at(exit, bst(y)))
;)
_(logic _(dryad "disj:bst_R") \bool disj_same_bst_reach(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, bst_reach(y))) ==> \at(enter, bst_reach(y)) == \at(exit, bst_reach(y)))
;)
_(logic _(dryad "disj:bst_keys") \bool disj_same_bst_keys(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, bst_reach(y))) ==> \at(enter, bst_keys(y)) == \at(exit, bst_keys(y)))
;)
_(logic \bool disj_same_bst_all(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	disj_same_bst(\at(enter, heaplet), y, enter, exit)
	&& disj_same_bst_reach(\at(enter, heaplet), y, enter, exit)
	&& disj_same_bst_keys(\at(enter, heaplet), y, enter, exit)
;)
_(logic _(dryad "disj:sortl") \bool disj_same_sortl(\oset heaplet, struct l_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, sortl_reach(y))) ==> \at(enter, sortl(y)) == \at(exit, sortl(y)))
;)
_(logic _(dryad "disj:sortl_R") \bool disj_same_sortl_reach(\oset heaplet, struct l_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, sortl_reach(y))) ==> \at(enter, sortl_reach(y)) == \at(exit, sortl_reach(y)))
;)
_(logic _(dryad "disj:sortl_keys") \bool disj_same_sortl_keys(\oset heaplet, struct l_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, sortl_reach(y))) ==> \at(enter, sortl_keys(y)) == \at(exit, sortl_keys(y)))
;)
_(logic \bool disj_same_sortl_all(\oset heaplet, struct l_node * y, \state enter, \state exit) =
	disj_same_sortl(\at(enter, heaplet), y, enter, exit)
	&& disj_same_sortl_reach(\at(enter, heaplet), y, enter, exit)
	&& disj_same_sortl_keys(\at(enter, heaplet), y, enter, exit)
;)


// -------------------------------- dummy abstract function --------------------------------
_(abstract _(dryad "end") void end_b_node_defs(struct b_node * x) ;)

//typedef struct l_node {
//	struct l_node * next;
//	int key;
//} LNode;


// -------------------------- base ------------------------------------------
_(abstract _(dryad "base:sortl") \bool sortl(struct l_node * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
;)
_(abstract _(dryad "base:sortl_R") \oset sortl_reach(struct l_node * hd)
	_(reads \universe())
	_(ensures (hd != NULL) ==> \oset_in(hd, \result))
	_(ensures (hd == NULL) ==> (\result == \oset_empty()))
;)
_(abstract _(dryad "base:sortl_keys") \intset sortl_keys(struct l_node * hd)
	_(reads \universe())
	_(ensures hd != NULL ==> \intset_in(hd->key, \result))
	_(ensures hd == NULL ==> (\result == \intset_empty()))
;)

// ------------------------------- unfold ------------------------------------------
_(logic _(dryad "unfold:sortl") \bool unfold_sortl(struct l_node * hd) =
	(hd != NULL ==>
		(sortl(hd) <==>
			(sortl(hd->next) &&
			!\oset_in(hd, sortl_reach(hd->next)) &&
			\intset_lt_one1(hd->key, sortl_keys(hd->next)) ) ) ) 
;)

_(logic _(dryad "unfold:sortl_R") \bool unfold_sortl_reach(struct l_node * hd) =
	(hd != NULL ==>
		(sortl_reach(hd) == \oset_union(sortl_reach(hd->next), \oset_singleton(hd))) ) 
;)

_(logic _(dryad "unfold:sortl_keys") \bool unfold_sortl_keys(struct l_node * hd) =
	(hd != NULL ==> 
		(sortl_keys(hd) == (\intset_union(sortl_keys(hd->next), \intset_singleton(hd->key))))) 
;)

_(logic \bool unfold_sortl_all(struct l_node * x) =
	unfold_sortl(x)
  && unfold_sortl_reach(x)
  && unfold_sortl_keys(x)
;)
// -------------------------------- same -------------------------------------------
_(logic _(dryad "same:sortl") \bool same_sortl(struct l_node * x, \state enter, \state exit) =
	\at(enter, sortl(x)) == \at(exit, sortl(x))
;)
_(logic _(dryad "same:sortl_R") \bool same_sortl_reach(struct l_node * x, \state enter, \state exit) =
	\at(enter, sortl_reach(x)) == \at(exit, sortl_reach(x))
;)
_(logic _(dryad "same:sortl_keys") \bool same_sortl_keys(struct l_node * x, \state enter, \state exit) =
	\at(enter, sortl_keys(x)) == \at(exit, sortl_keys(x))
;)
_(logic \bool same_sortl_all(struct l_node * x, \state enter, \state exit) =
	same_sortl(x, enter, exit)
	&& same_sortl_reach(x, enter, exit)
	&& same_sortl_keys(x, enter, exit)
;)

// ----------------------------  cond same  ----------------------------------------
_(logic _(dryad "cond:sortl") \bool cond_same_sortl(struct l_node * x, struct l_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, sortl_reach(y))) ==> \at(enter, sortl(y)) == \at(exit, sortl(y)))
;)
_(logic _(dryad "cond:sortl_R") \bool cond_same_sortl_reach(struct l_node * x, struct l_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, sortl_reach(y))) ==> \at(enter, sortl_reach(y)) == \at(exit, sortl_reach(y)))
;)
_(logic _(dryad "cond:sortl_keys") \bool cond_same_sortl_keys(struct l_node * x, struct l_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, sortl_reach(y))) ==> \at(enter, sortl_keys(y)) == \at(exit, sortl_keys(y)))
;)
_(logic \bool cond_same_sortl_all(struct l_node * x, struct l_node * y, \state enter, \state exit) =
	cond_same_sortl(x, y, enter, exit)
	&& cond_same_sortl_reach(x, y, enter, exit)
	&& cond_same_sortl_keys(x, y, enter, exit)
;)

_(logic _(dryad "cond:bst") \bool cond_same_bst(struct l_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y))) ==> \at(enter, bst(y)) == \at(exit, bst(y)))
;)
_(logic _(dryad "cond:bst_R") \bool cond_same_bst_reach(struct l_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y))) ==> \at(enter, bst_reach(y)) == \at(exit, bst_reach(y)))
;)
_(logic _(dryad "cond:bst_keys") \bool cond_same_bst_keys(struct l_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y))) ==> \at(enter, bst_keys(y)) == \at(exit, bst_keys(y)))
;)

_(logic \bool cond_same_bst_all(struct l_node * x, struct b_node * y, \state enter, \state exit) =
	cond_same_bst(x, y, enter, exit)
	&& cond_same_bst_reach(x, y, enter, exit)
	&& cond_same_bst_keys(x, y, enter, exit)
;)

// ----------------------------  disj same  ----------------------------------------
/*
_(logic _(dryad "disj:sortl") \bool disj_same_sortl(\oset heaplet, struct l_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, sortl_reach(y))) ==> \at(enter, sortl(y)) == \at(exit, sortl(y)))
;)
_(logic _(dryad "disj:sortl_R") \bool disj_same_sortl_reach(\oset heaplet, struct l_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, sortl_reach(y))) ==> \at(enter, sortl_reach(y)) == \at(exit, sortl_reach(y)))
;)
_(logic _(dryad "disj:sortl_keys") \bool disj_same_sortl_keys(\oset heaplet, struct l_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, sortl_reach(y))) ==> \at(enter, sortl_keys(y)) == \at(exit, sortl_keys(y)))
;)
_(logic \bool disj_same_sortl_all(\oset heaplet, struct l_node * y, \state enter, \state exit) =
	disj_same_sortl(\at(enter, heaplet), y, enter, exit)
	&& disj_same_sortl_reach(\at(enter, heaplet), y, enter, exit)
	&& disj_same_sortl_keys(\at(enter, heaplet), y, enter, exit)
;)
*/
/*
_(logic _(dryad "disj:bst") \bool disj_same_bst(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, bst_reach(y))) ==> \at(enter, bst(y)) == \at(exit, bst(y)))
;)
_(logic _(dryad "disj:bst_R") \bool disj_same_bst_reach(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, bst_reach(y))) ==> \at(enter, bst_reach(y)) == \at(exit, bst_reach(y)))
;)
_(logic _(dryad "disj:bst_keys") \bool disj_same_bst_keys(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, bst_reach(y))) ==> \at(enter, bst_keys(y)) == \at(exit, bst_keys(y)))
;)

_(logic \bool disj_same_bst_all(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	disj_same_bst(\at(enter, heaplet), y, enter, exit)
	&& disj_same_bst_reach(\at(enter, heaplet), y, enter, exit)
	&& disj_same_bst_keys(\at(enter, heaplet), y, enter, exit)
;)
*/

_(abstract _(dryad "end") void end_l_node_defs(struct l_node * x) ;)

#endif
