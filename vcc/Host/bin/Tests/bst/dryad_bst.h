#ifndef DRYAD_BST_DEFS_H
#define DRYAD_BST_DEFS_H

#include <vcc.h>
#include <stdlib.h>

typedef 
_(dryad "bst:bst_R:bst_keys")
struct b_node {
	struct b_node * left;
	struct b_node * right;
	int key;
} BNode;

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
										                 \intset_union(bst_keys(root->left), 
                       													   bst_keys(root->right))))
   ) 
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
	  (\at(enter, bst_reach(x)) == \at(exit, bst_reach(x)))
;)
_(logic _(dryad "same:bst_keys") \bool same_bst_keys(struct b_node * x, \state enter, \state exit) =
	(\at(enter, bst_keys(x)) == \at(exit, bst_keys(x)))
;)
_(logic \bool same_bst_all(struct b_node * x, \state enter, \state exit) =
	same_bst(x, enter, exit)
	&& same_bst_reach(x, enter, exit)
	&& same_bst_keys(x, enter, exit)
;)

// ----------------------------  cond same  ------------------------------------------------
_(logic _(dryad "cond:bst") \bool cond_same_bst(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y)))) ==> \at(enter, bst(y)) == \at(exit, bst(y))
;)
_(logic _(dryad "cond:bst_R") \bool cond_same_bst_reach(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y)))) ==> (\at(enter, bst_reach(y)) == \at(exit, bst_reach(y)))
;)
_(logic _(dryad "cond:bst_keys") \bool cond_same_bst_keys(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y)))) ==> (\at(enter, bst_keys(y)) == \at(exit, bst_keys(y)))
;)
_(logic \bool cond_same_bst_all(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	cond_same_bst(x, y, enter, exit)
	&& cond_same_bst_reach(x, y, enter, exit)
	&& cond_same_bst_keys(x, y, enter, exit)
;)

// ----------------------------  disj same  ------------------------------------------------
_(logic _(dryad "disj:bst") \bool disj_same_bst(\oset heaplet_pre, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet_pre), \at(enter, bst_reach(y)))) ==> \at(enter, bst(y)) == \at(exit, bst(y))
;)
_(logic _(dryad "disj:bst_R") \bool disj_same_bst_reach(\oset heaplet_pre, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet_pre), \at(enter, bst_reach(y)))) ==> (\at(enter, bst_reach(y)) == \at(exit, bst_reach(y)))
;)
_(logic _(dryad "disj:bst_keys") \bool disj_same_bst_keys(\oset heaplet_pre, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet_pre), \at(enter, bst_reach(y)))) ==> (\at(enter, bst_keys(y)) == \at(exit, bst_keys(y)))
;)
_(logic \bool disj_same_bst_all(\oset heaplet_pre, struct b_node * y, \state enter, \state exit) =
	disj_same_bst(heaplet_pre, y, enter, exit)
	&& disj_same_bst_reach(heaplet_pre, y, enter, exit)
	&& disj_same_bst_keys(heaplet_pre, y, enter, exit)
;)

// -------------------------------- dummy abstract function --------------------------------
_(abstract _(dryad "end") void end_b_node_defs(struct b_node * x) ;)

#endif
