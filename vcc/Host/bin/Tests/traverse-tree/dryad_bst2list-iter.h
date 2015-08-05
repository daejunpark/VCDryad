#ifndef DRYAD_BST2SORTED_ITER_DEFS_H
#define DRYAD_BST2SORTED_ITER_DEFS_H

#include <vcc.h>
#include <stdlib.h>
//#include "intbag_defs.h"
//#include "intset_defs.h"

typedef 
_(dryad "bst:bst_R:bst_keys:sortl:sortl_R:sortl_keys:stack:stack_R:stack_keys")
struct node 
{
	struct node * next;
	struct node * left;
	struct node * right;
	struct node * tree;
	int key;
} Node;

// -------------------------- base ------------------------------------------
_(abstract _(dryad "base:bst") \bool bst(struct node * root)
	_(reads \universe())
	_(ensures (root == NULL) ==> \result)
;)
_(abstract _(dryad "base:bst_R") \oset bst_reach(struct node * root)
	_(reads \universe())
	_(ensures (root != NULL) ==> \oset_in(root, \result))
	_(ensures (root == NULL) ==> (\result == \oset_empty()))
;)
_(abstract _(dryad "base:bst_keys") \intset bst_keys(struct node * root)
	_(reads \universe())
	_(ensures (root != NULL) ==> \intset_in(root->key, \result))
	//_(ensures (root != NULL && (root->next != NULL || root->tree != NULL)) ==> (\result == \intset_empty()))
	_(ensures root == NULL ==> (\result == \intset_empty()))
;)

_(abstract _(dryad "base:sortl") \bool sortl(struct node * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
;)
_(abstract _(dryad "base:sortl_R") \oset sortl_reach(struct node * hd)
	_(reads \universe())
	_(ensures (hd != NULL) ==> \oset_in(hd, \result))
	//_(ensures (hd != NULL && (hd->left != NULL || hd->right != NULL || hd->tree != NULL)) ==> (\result == \oset_empty()))
	_(ensures (hd == NULL) ==> (\result == \oset_empty()))
;)
_(abstract _(dryad "base:sortl_keys") \intset sortl_keys(struct node * hd)
	_(reads \universe())
	_(ensures (hd != NULL) ==> \intset_in(hd->key, \result))
	//_(ensures (hd != NULL && (hd->left == NULL || hd->right == NULL || hd->tree == NULL)) ==> (\result == \intset_empty))
	_(ensures hd == NULL ==> (\result == \intset_empty()))
;)

_(abstract _(dryad "base:stack") \bool stack(struct node * st)
	_(reads \universe())
	_(ensures (st == NULL) ==> \result)
;)
_(abstract _(dryad "base:stack_R") \oset stack_reach(struct node * st)
	_(reads \universe())
	_(ensures (st != NULL) ==> \oset_in(st, \result))
	_(ensures (st == NULL) ==> (\result == \oset_empty()))
;)
_(abstract _(dryad "base:stack_keys") \intset stack_keys(struct node * st)
	_(reads \universe())
	_(ensures (st != NULL) ==> \intset_in(st->key, \result))
	_(ensures (st == NULL) ==> (\result == \intset_empty()))
;)

// ---------------------------- unfold --------------------------------------
_(logic _(dryad "unfold:bst") \bool unfold_bst(struct node * root) =
	(root != NULL ==>
		(bst(root) <==>
			(bst(root->left) && bst(root->right) 
			&& (! \oset_in(root, \oset_union(bst_reach(root->left), bst_reach(root->right)))) 
			&& \oset_disjoint(bst_reach(root->left), bst_reach(root->right)) 
			&& !\intset_in(root->key, \intset_union(bst_keys(root->left), bst_keys(root->right)))
			&& \intset_disjoint(bst_keys(root->left), bst_keys(root->right))
			&& \intset_le_one2(bst_keys(root->left), root->key) 
			&& \intset_le_one1(root->key, bst_keys(root->right))  
			&& root->next == NULL && root->tree == NULL ) ) ) 
;)
_(logic _(dryad "unfold:bst_R") \bool unfold_bst_reach(struct node * root) =
	(root != NULL ==>
		(bst_reach(root) == \oset_union(\oset_singleton(root),  
                                    \oset_union(bst_reach(root->left), bst_reach(root->right)))))
;)
_(logic _(dryad "unfold:bst_keys") \bool unfold_bst_keys(struct node * root) =
	(root != NULL ==>
		(bst_keys(root) == \intset_union(\intset_singleton(root->key), 
	  									 \intset_union(bst_keys(root->left), 
													  bst_keys(root->right))) 
			&& \intset_subset(\intset_singleton(root->key), bst_keys(root))	
			&& \intset_subset(bst_keys(root->left),  bst_keys(root)) 
			&& \intset_subset(bst_keys(root->right), bst_keys(root)) ))  
;)
_(logic \bool unfold_bst_all(struct node * x) =
	unfold_bst(x)
  && unfold_bst_reach(x)
	&& unfold_bst_keys(x)
;)

_(logic _(dryad "unfold:sortl") \bool unfold_sortl(struct node * hd) =
	(hd != NULL ==>
		(sortl(hd) <==>
			(sortl(hd->next) 
			&& !\oset_in(hd, sortl_reach(hd->next)) 
			&& \intset_le_one1(hd->key, sortl_keys(hd->next))  
			&& hd->left == NULL && hd->right == NULL && hd->tree == NULL ) ) ) 
;)

_(logic  _(dryad "unfold:sortl_R") \bool unfold_sortl_reach(struct node * hd) =
	(hd != NULL ==> (sortl_reach(hd) == \oset_union(sortl_reach(hd->next), \oset_singleton(hd))) ) 
;)

_(logic _(dryad "unfold:sortl_keys") \bool unfold_sortl_keys(struct node * hd) =
	(hd != NULL ==> 
		(sortl_keys(hd) == (\intset_union(sortl_keys(hd->next), 
										  \intset_singleton(hd->key) ))) )
;)

_(logic \bool unfold_sortl_all(struct node * x) =
	unfold_sortl(x)
  && unfold_sortl_reach(x)
	&& unfold_sortl_keys(x)
;)

_(logic _(dryad "unfold:stack") \bool unfold_stack(struct node * st) =
	(st != NULL ==>
		(stack(st) <==>
			(stack(st->next)
			 && !\oset_in(st, stack_reach(st->next))
			 && !\oset_in(st, bst_reach(st->tree))
			 && \oset_disjoint(stack_reach(st->next), bst_reach(st->tree))
			 && st->tree != NULL && bst(st->tree)
			 && \intset_le(stack_keys(st->next), bst_keys(st->tree)) 
			 && st->left == NULL && st->right == NULL ) ) )
;)

_(logic _(dryad "unfold:stack_R") \bool unfold_stack_reach(struct node * st) =
	(st != NULL && st->tree != NULL ==>
		(stack_reach(st) == \oset_union(\oset_singleton(st),
                                    \oset_union(stack_reach(st->next), bst_reach(st->tree)) ) ) )
;)

_(logic _(dryad "unfold:stack_keys") \bool unfold_stack_keys(struct node * st) =
	(st != NULL && st->tree != NULL ==>
	 	(stack_keys(st) == (\intset_union(stack_keys(st->next),
	                									  bst_keys(st->tree) )) ) 
		&& \intset_subset(bst_keys(st->tree), stack_keys(st)) 
  )
;)
_(logic \bool unfold_stack_all(struct node * x) =
	unfold_stack(x)
	&& unfold_stack_reach(x)
	&& unfold_stack_keys(x)
;)


// -------------------------------- same --------------------------------------------------
_(logic _(dryad "same:bst") \bool same_bst(struct node * x, \state enter, \state exit) =
	\at(enter, bst(x)) == \at(exit, bst(x))
;)
_(logic _(dryad "same:bst_R") \bool same_bst_reach(struct node * x, \state enter, \state exit) =
	\at(enter, bst_reach(x)) == \at(exit, bst_reach(x))
;)
_(logic _(dryad "same:bst_keys") \bool same_bst_keys(struct node * x, \state enter, \state exit) =
	\at(enter, bst_keys(x)) == \at(exit, bst_keys(x))
;)
_(logic \bool same_bst_all(struct node * x, \state enter, \state exit) =
	same_bst(x, enter, exit)
	&& same_bst_reach(x, enter, exit)
	&& same_bst_keys(x, enter, exit)
;)

_(logic _(dryad "same:sortl") \bool same_sortl(struct node * x, \state enter, \state exit) =
	\at(enter, sortl(x)) == \at(exit, sortl(x))
;)
_(logic _(dryad "same:sortl_R") \bool same_sortl_reach(struct node * x, \state enter, \state exit) =
	\at(enter, sortl_reach(x)) == \at(exit, sortl_reach(x))
;)
_(logic _(dryad "same:sortl_keys") \bool same_sortl_keys(struct node * x, \state enter, \state exit) =
	\at(enter, sortl_keys(x)) == \at(exit, sortl_keys(x))
;)
_(logic \bool same_sortl_all(struct node * x, \state enter, \state exit) =
	same_sortl(x, enter, exit)
	&& same_sortl_reach(x, enter, exit)
	&& same_sortl_keys(x, enter, exit)
;)

_(logic _(dryad "same:stack") \bool same_stack(struct node * x, \state enter, \state exit) =
	\at(enter, stack(x)) == \at(exit, stack(x))
;)
_(logic _(dryad "same:stack_R") \bool same_stack_reach(struct node * x, \state enter, \state exit) =
	\at(enter, stack_reach(x)) == \at(exit, stack_reach(x))
;)
_(logic _(dryad "same:stack_keys") \bool same_stack_keys(struct node * x, \state enter, \state exit) =
	\at(enter, stack_keys(x)) == \at(exit, stack_keys(x))
;)
_(logic \bool same_stack_all(struct node * x, \state enter, \state exit) =
	same_stack(x, enter, exit)
	&& same_stack_reach(x, enter, exit)
	&& same_stack_keys(x, enter, exit)
;)


// ----------------------------  cond same  ------------------------------------------------
_(logic _(dryad "cond:bst") \bool cond_same_bst(struct node * x, struct node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y))) ==> \at(enter, bst(y)) == \at(exit, bst(y)))
;)
_(logic _(dryad "cond:bst_R") \bool cond_same_bst_reach(struct node * x, struct node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y))) ==> \at(enter, bst_reach(y)) == \at(exit, bst_reach(y)))
;)
_(logic _(dryad "cond:bst_keys") \bool cond_same_bst_keys(struct node * x, struct node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, bst_reach(y))) ==> \at(enter, bst_keys(y)) == \at(exit, bst_keys(y)))
;)
_(logic \bool cond_same_bst_all(struct node * x, struct node * y, \state enter, \state exit) =
	cond_same_bst(x, y, enter, exit)
	&& cond_same_bst_reach(x, y, enter, exit)
	&& cond_same_bst_keys(x, y, enter, exit)
;)

_(logic _(dryad "cond:sortl") \bool cond_same_sortl(struct node * x, struct node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, sortl_reach(y))) ==> \at(enter, sortl(y)) == \at(exit, sortl(y)))
;)
_(logic _(dryad "cond:sortl_R") \bool cond_same_sortl_reach(struct node * x, struct node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, sortl_reach(y))) ==> \at(enter, sortl_reach(y)) == \at(exit, sortl_reach(y)))
;)
_(logic _(dryad "cond:sortl_keys") \bool cond_same_sortl_keys(struct node * x, struct node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, sortl_reach(y))) ==> \at(enter, sortl_keys(y)) == \at(exit, sortl_keys(y)))
;)
_(logic \bool cond_same_sortl_all(struct node * x, struct node * y, \state enter, \state exit) =
	cond_same_sortl(x, y, enter, exit)
	&& cond_same_sortl_reach(x, y, enter, exit)
	&& cond_same_sortl_keys(x, y, enter, exit)
;)

_(logic _(dryad "cond:stack") \bool cond_same_stack(struct node * x, struct node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, stack_reach(y))) ==> \at(enter, stack(y)) == \at(exit, stack(y)))
;)
_(logic _(dryad "cond:stack_R") \bool cond_same_stack_reach(struct node * x, struct node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, stack_reach(y))) ==> \at(enter, stack_reach(y)) == \at(exit, stack_reach(y)))
;)
_(logic _(dryad "cond:stack_keys") \bool cond_same_stack_keys(struct node * x, struct node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, stack_reach(y))) ==> \at(enter, stack_keys(y)) == \at(exit, stack_keys(y)))
;)
_(logic \bool cond_same_stack_all(struct node * x, struct node * y, \state enter, \state exit) =
	cond_same_stack(x, y, enter, exit)
	&& cond_same_stack_reach(x, y, enter, exit)
	&& cond_same_stack_keys(x, y, enter, exit)
;)

// -------------------------------- dummy abstract function --------------------------------
_(abstract _(dryad "end") void end_node_defs(struct node * x) ;)

/// ----------------------------- axioms --------------------------------------------------

//???
_(axiom \forall struct node * x, y; (x == NULL) ==> !\oset_in(x, stack_reach(y)))
_(axiom \forall struct node * x, y; (x == NULL) ==> !\oset_in(x, sortl_reach(y)))
_(axiom \forall struct node * x, y; (x == NULL) ==> !\oset_in(x, bst_reach(y)))


#endif
