#ifndef DRYAD_TREAP_DEFS_H
#define DRYAD_TREAP_DEFS_H

#include <vcc.h>
#include <stdlib.h>
//#include "intbag_defs.h"
//#include "intset_defs.h"

typedef 
_(dryad "treap:treap_R:treap_keys:treap_prios")
struct b_node {
	struct b_node * left;
	struct b_node * right;
	int key;
  int prio;
} BNode;

// -------------------------- base ------------------------------------------
_(abstract _(dryad "base:treap") \bool treap(struct b_node * root)
	_(reads \universe())
	_(ensures (root == NULL) ==> \result)
;)
_(abstract _(dryad "base:treap_R") \oset treap_reach(struct b_node * root)
	_(reads \universe())
	_(ensures (root != NULL) ==> \oset_in(root, \result))
	_(ensures (root == NULL) ==> (\result == \oset_empty()))
;)
_(abstract _(dryad "base:treap_keys") \intset treap_keys(struct b_node * root)
	_(reads \universe())
	_(ensures root != NULL ==> \intset_in(root->key, \result))
	_(ensures root == NULL ==> (\result == \intset_empty()))
;)
_(abstract _(dryad "base:treap_prios") \intset treap_prios(struct b_node * root)
	_(reads \universe())
	_(ensures root != NULL ==> \intset_in(root->prio, \result))
	_(ensures root == NULL ==> (\result == \intset_empty()))
;)

// ---------------------------- unfold --------------------------------------
_(logic _(dryad "unfold:treap") \bool unfold_treap(struct b_node * root) =
	(root != NULL ==>
		(treap(root) <==>
			(treap(root->left) && treap(root->right) 
			&& (! \oset_in(root, \oset_union(treap_reach(root->left), treap_reach(root->right)))) 
      && !\intset_in(root->key,  \intset_union(treap_keys (root->left), treap_keys( root->right)))
      && !\intset_in(root->prio, \intset_union(treap_prios(root->left), treap_prios(root->right)))
			&& \oset_disjoint(treap_reach(root->left), treap_reach(root->right))
      && \intset_disjoint(treap_keys(root->left), treap_keys(root->right))
      && \intset_disjoint(treap_prios(root->left), treap_prios(root->right))
      && \intset_lt_one2(treap_keys(root->left), root->key)
      && \intset_lt_one1(root->key, treap_keys(root->right)) 
      && \intset_lt_one2(treap_prios(root->left),  root->prio)
      && \intset_lt_one2(treap_prios(root->right), root->prio)
      ) ) )
;)
_(logic _(dryad "unfold:treap_R") \bool unfold_treap_reach(struct b_node * root) =
  (root != NULL ==>
		(treap_reach(root) == \oset_union(\oset_singleton(root), 
                                      \oset_union(treap_reach(root->left), treap_reach(root->right)))))
;)
_(logic _(dryad "unfold:treap_keys") \bool unfold_treap_keys(struct b_node * root) =
	(root != NULL ==>
		(treap_keys(root) == \intset_union(\intset_singleton(root->key), 
										                 \intset_union(treap_keys(root->left), 
                       													   treap_keys(root->right))))
   ) 
;)
_(logic _(dryad "unfold:treap_prios") \bool unfold_treap_prios(struct b_node * root) =
	(root != NULL ==>
		(treap_prios(root) == \intset_union(\intset_singleton(root->prio), 
										                 \intset_union(treap_prios(root->left), 
                       													   treap_prios(root->right))))
   ) 
;)
_(logic \bool unfold_treap_all(struct b_node * x) =
  unfold_treap(x)
	&& unfold_treap_reach(x)
	&& unfold_treap_keys(x)
	&& unfold_treap_prios(x)
;)

// -------------------------------- same --------------------------------------------------
_(logic _(dryad "same:treap") \bool same_treap(struct b_node * x, \state enter, \state exit) =
	\at(enter, treap(x)) == \at(exit, treap(x))
;)
_(logic _(dryad "same:treap_R")  \bool same_treap_reach(struct b_node * x, \state enter, \state exit) =
	\at(enter, treap_reach(x)) == \at(exit, treap_reach(x))
;)
_(logic _(dryad "same:treap_keys") \bool same_treap_keys(struct b_node * x, \state enter, \state exit) =
	\at(enter, treap_keys(x)) == \at(exit, treap_keys(x))
;)
_(logic _(dryad "same:treap_prios") \bool same_treap_prios(struct b_node * x, \state enter, \state exit) =
	\at(enter, treap_prios(x)) == \at(exit, treap_prios(x))
;)
_(logic \bool same_treap_all(struct b_node * x, \state enter, \state exit) =
	same_treap(x, enter, exit)
	&& same_treap_reach(x, enter, exit)
	&& same_treap_keys(x, enter, exit)
	&& same_treap_prios(x, enter, exit)
;)

// ----------------------------  cond same  ------------------------------------------------
_(logic _(dryad "cond:treap") \bool cond_same_treap(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, treap_reach(y))) ==> \at(enter, treap(y)) == \at(exit, treap(y)))
;)
_(logic _(dryad "cond:treap_R") \bool cond_same_treap_reach(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, treap_reach(y))) ==> \at(enter, treap_reach(y)) == \at(exit, treap_reach(y)))
;)
_(logic _(dryad "cond:treap_keys") \bool cond_same_treap_keys(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, treap_reach(y))) ==> \at(enter, treap_keys(y)) == \at(exit, treap_keys(y)))
;)
_(logic _(dryad "cond:treap_prios") \bool cond_same_treap_prios(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, treap_reach(y))) ==> \at(enter, treap_prios(y)) == \at(exit, treap_prios(y)))
;)
_(logic \bool cond_same_treap_all(struct b_node * x, struct b_node * y, \state enter, \state exit) =
	cond_same_treap(x, y, enter, exit)
	&& cond_same_treap_reach(x, y, enter, exit)
	&& cond_same_treap_keys(x, y, enter, exit)
	&& cond_same_treap_prios(x, y, enter, exit)
;)
// ----------------------------  disj same  ------------------------------------------------
_(logic _(dryad "disj:treap") \bool disj_same_treap(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, treap_reach(y))) ==> \at(enter, treap(y)) == \at(exit, treap(y)))
;)
_(logic _(dryad "disj:treap_R") \bool disj_same_treap_reach(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, treap_reach(y))) ==> \at(enter, treap_reach(y)) == \at(exit, treap_reach(y)))
;)
_(logic _(dryad "disj:treap_keys") \bool disj_same_treap_keys(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, treap_reach(y))) ==> \at(enter, treap_keys(y)) == \at(exit, treap_keys(y)))
;)
_(logic _(dryad "disj:treap_prios") \bool disj_same_treap_prios(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, treap_reach(y))) ==> \at(enter, treap_prios(y)) == \at(exit, treap_prios(y)))
;)
_(logic \bool disj_same_treap_all(\oset heaplet, struct b_node * y, \state enter, \state exit) =
	disj_same_treap(\at(enter, heaplet), y, enter, exit)
	&& disj_same_treap_reach(\at(enter, heaplet), y, enter, exit)
	&& disj_same_treap_keys(\at(enter, heaplet), y, enter, exit)
	&& disj_same_treap_prios(\at(enter, heaplet), y, enter, exit)
;)


// -------------------------------- dummy abstract function --------------------------------
_(abstract _(dryad "end") void end_b_node_defs(struct b_node * x) ;)

/// ----------------------------- axioms --------------------------------------------------
//_(axiom \forall \oset os1, os2, os3; \disjoint(os1, (os2 \union os3)) <==> (\disjoint(os1, os2) && \disjoint(os1, os3)))
//_(axiom \forall \oset os1, os2; \disjoint(os1, os2) == \disjoint(os2, os1))
//_(axiom \forall \oset os1, os2; \disjoint(os1, os2) <==> \subset(os1, (\universe() \diff os2)))
//_(axiom \forall \oset os1, os2; \forall \object o; (os1 == (os2 \union {o})) ==> \subset(os2, os1)) // [sll-reverse]

#endif
