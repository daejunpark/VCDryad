#ifndef DRYAD_DLL_DEFS_H
#define DRYAD_DLL_DEFS_H

#include <vcc.h>
// ------------------------
#include <stdlib.h>

typedef
_(dryad "dll:dll_R:keys:dll-rev:dll-rev_R:keys-rev")
struct d_node {
  int key;
  struct d_node * prev;
  struct d_node * next;
} DLNode;


_(abstract _(dryad "base:dll") \bool dll(struct d_node * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
	;)

_(abstract _(dryad "base:dll_R") \oset dll_reach(struct d_node * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
			&& ((hd == NULL) ==> (\result == \oset_empty())))
	;)

_(abstract _(dryad "base:keys") \intset dll_keys(struct d_node * hd) // [key]
	_(reads \universe())
	_(ensures (hd != NULL ==> \intset_in(hd->key, \result)))
	_(ensures (hd == NULL ==> (\result == \intset_empty())))
	;)

_(abstract _(dryad "base:dll-rev") \bool dll_rev(struct d_node * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
	;)

_(abstract _(dryad "base:dll-rev_R") \oset dll_reach_rev(struct d_node * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
			&& ((hd == NULL) ==> (\result == \oset_empty())))
	;)

_(abstract _(dryad "base:keys") \intset dll_keys_rev(struct d_node * hd) // [key]
	_(reads \universe())
	_(ensures (hd != NULL ==> \intset_in(hd->key, \result)))
	_(ensures (hd == NULL ==> (\result == \intset_empty())))
	;)


// ----------------------------------------------------------------------------------------------------------------------------
_(logic _(dryad "unfold:dll") \bool unfold_dll(struct d_node * hd) =
	(hd != NULL ==>
		(dll(hd) <==> 
			(dll(hd->next) && 
			(hd->next != NULL ==> hd->next->prev == hd) &&
			(! \oset_in(hd, dll_reach(hd->next))) ) ) ) 
	;)

_(logic _(dryad "unfold:dll_R")  \bool unfold_dll_reach(struct d_node * hd) =
	(hd != NULL ==>	(dll_reach(hd) == \oset_union(dll_reach(hd->next), \oset_singleton(hd))) ) 	;)


_(logic _(dryad "unfold:keys") \bool unfold_dll_keys(struct d_node * hd) =
		(hd != NULL ==> (dll_keys(hd) == (\intset_union(dll_keys(hd->next), \intset_singleton(hd->key))))) ;)

_(logic _(dryad "unfold:dll-rev") \bool unfold_dll_rev(struct d_node * hd) =
	(hd != NULL ==>
		(dll(hd) <==> 
			(dll_rev(hd->prev) && 
			(hd->prev != NULL ==> hd->prev->next == hd) &&
			(! \oset_in(hd, dll_reach_rev(hd->prev))) ) ) ) 
	;)

_(logic _(dryad "unfold:dll-rev_R")  \bool unfold_dll_reach_rev(struct d_node * hd) =
	(hd != NULL ==>	(dll_reach_rev(hd) == \oset_union(dll_reach_rev(hd->prev), \oset_singleton(hd))) ) ;)

_(logic _(dryad "unfold:keys-rev") \bool unfold_dll_keys_rev(struct d_node * hd) =
  (hd != NULL ==> (dll_keys_rev(hd) == (\intset_union(dll_keys_rev(hd->prev), \intset_singleton(hd->key))))) ;)


_(logic _(dryad "unfold:all-un") \bool unfold_dll_all(struct d_node * x) =
	unfold_dll(x)
	&& unfold_dll_reach(x)
	&& unfold_dll_keys(x)
	&& unfold_dll_rev(x)
	&& unfold_dll_reach_rev(x)
	&& unfold_dll_keys_rev(x)
	;)


// -----------------------------------------------------------------------------------------------------
_(logic _(dryad "same:dll") \bool same_dll(struct d_node * x, \state enter, \state exit) =
	\at(enter, dll(x)) == \at(exit, dll(x))
;)
_(logic _(dryad "same:dll_R") \bool same_dll_reach(struct d_node * x, \state enter, \state exit) = 
	\at(enter, dll_reach(x)) == \at(exit, dll_reach(x)) 
;)
_(logic _(dryad "same:keys") \bool same_dll_keys(struct d_node * x, \state enter, \state exit) =
	\at(enter, dll_keys(x)) == \at(exit, dll_keys(x))
;)
_(logic _(dryad "same:dll-rev") \bool same_dll_rev(struct d_node * x, \state enter, \state exit) =
	\at(enter, dll_rev(x)) == \at(exit, dll_rev(x))
;)
_(logic _(dryad "same:dll-rev_R") \bool same_dll_reach_rev(struct d_node * x, \state enter, \state exit) = 
	\at(enter, dll_reach_rev(x)) == \at(exit, dll_reach_rev(x)) 
;)
_(logic _(dryad "same:keys-rev") \bool same_dll_keys_rev(struct d_node * x, \state enter, \state exit) =
	\at(enter, dll_keys_rev(x)) == \at(exit, dll_keys_rev(x))
;)
_(logic _(dryad "same:all-un") \bool same_dll_all(struct d_node * x, \state enter, \state exit) = 
	same_dll(x, enter, exit) 
	&& same_dll_reach(x, enter, exit)
	&& same_dll_keys(x, enter, exit)
	&& same_dll_rev(x, enter, exit) 
	&& same_dll_reach_rev(x, enter, exit)
	&& same_dll_keys_rev(x, enter, exit)  
;)
// ------------------------------------------------------------------------------------------------------

_(logic _(dryad "cond:dll") \bool cond_same_dll(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dll_reach(y)))) ==> \at(enter, dll(y)) == \at(exit, dll(y))
;)
_(logic _(dryad "cond:dll_R") \bool cond_same_dll_reach(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dll_reach(y)))) ==> \at(enter, dll_reach(y)) == \at(exit, dll_reach(y))
;)
_(logic _(dryad "cond:keys") \bool cond_same_dll_keys(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dll_reach(y)))) ==> \at(enter, dll_keys(y)) == \at(exit, dll_keys(y))
;)
_(logic _(dryad "cond:dll-rev") \bool cond_same_dll_rev(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dll_reach_rev(y)))) ==> \at(enter, dll_rev(y)) == \at(exit, dll_rev(y))
;)
_(logic _(dryad "cond:dll-rev_R") \bool cond_same_dll_reach_rev(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dll_reach_rev(y)))) ==> \at(enter, dll_reach_rev(y)) == \at(exit, dll_reach_rev(y))
;)
_(logic _(dryad "cond:keys-rev") \bool cond_same_dll_keys_rev(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dll_reach_rev(y)))) ==> \at(enter, dll_keys_rev(y)) == \at(exit, dll_keys_rev(y))
;)
_(logic _(dryad "cond:all-un") \bool cond_same_dll_all(struct d_node * x, struct d_node * y, \state enter, \state exit) =
	cond_same_dll(x, y, enter, exit) 
	&& cond_same_dll_reach(x, y, enter, exit)
	&& cond_same_dll_keys(x, y, enter, exit)
	&& cond_same_dll_rev(x, y, enter, exit) 
	&& cond_same_dll_reach_rev(x, y, enter, exit)
	&& cond_same_dll_keys_rev(x, y, enter, exit)
;)

// dummy function denoting the end of dl_node defs
_(abstract _(dryad "end") void end_dl_node_defs(struct d_node * x) ;)
// ---------------------------------------------------------------------------------------------------------

#endif
