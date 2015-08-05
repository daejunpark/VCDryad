#ifndef DRYAD_SLAVE_DLL_DEFS_H
#define DRYAD_SLAVE_DLL_DEFS_H

#include <vcc.h>
// ------------------------
#include <stdlib.h>

typedef
_(dryad "dllnext:dllnext_R:dllprev:dllprev_R")
struct list_head {
  struct list_head * prev;
  struct list_head * next;
  int inserted;
};


_(abstract _(dryad "base:dllnext") \bool dllnext(struct list_head * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
	;)

_(abstract _(dryad "base:dllnext_R") \oset dllnext_reach(struct list_head * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
			&& ((hd == NULL) ==> (\result == \oset_empty())))
	;)
_(abstract _(dryad "base:dllprev") \bool dllprev(struct list_head * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
	;)

_(abstract _(dryad "base:dllprev_R") \oset dllprev_reach(struct list_head * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
			&& ((hd == NULL) ==> (\result == \oset_empty())))
	;)


// ----------------------------------------------------------------------------------------------------------------------------
_(logic _(dryad "unfold:dllnext") \bool unfold_dllnext(struct list_head * hd) =
	(hd != NULL ==>
		(dllnext(hd) <==> 
			(dllnext(hd->next) && 
			(hd->next != NULL ==> hd->next->prev == hd) &&
			(! \oset_in(hd, dllnext_reach(hd->next))) ) &&
      hd->inserted == 1
      ) ) 
	;)

_(logic _(dryad "unfold:dllnext_R")  \bool unfold_dllnext_reach(struct list_head * hd) =
	(hd != NULL ==>	(dllnext_reach(hd) == \oset_union(dllnext_reach(hd->next), \oset_singleton(hd))) ) ;)

_(logic _(dryad "unfold:dllprev") \bool unfold_dllprev(struct list_head * hd) =
	(hd != NULL ==>
		(dllprev(hd) <==> 
			(dllprev(hd->prev) && 
			(hd->prev != NULL ==> hd->prev->next == hd) &&
			(! \oset_in(hd, dllprev_reach(hd->prev))) ) &&
      hd->inserted == 1
      ) ) 
	;)
_(logic _(dryad "unfold:dllprev_R")  \bool unfold_dllprev_reach(struct list_head * hd) =
	(hd != NULL ==>	(dllprev_reach(hd) == \oset_union(dllprev_reach(hd->prev), \oset_singleton(hd))) ) ;)


_(logic \bool unfold_dllnext_all(struct list_head * x) =
   unfold_dllnext(x)
   && unfold_dllnext_reach(x)
;)

// ----------------------------------------------------------------------------------------------------------------------------

_(logic _(dryad "same:dllnext") \bool same_dllnext(struct list_head * x, \state enter, \state exit) =
	\at(enter, dllnext(x)) == \at(exit, dllnext(x))
;)
_(logic _(dryad "same:dllnext_R") \bool same_dllnext_reach(struct list_head * x, \state enter, \state exit) = 
	\at(enter, dllnext_reach(x)) == \at(exit, dllnext_reach(x)) 
;)

_(logic _(dryad "same:dllprev") \bool same_dllprev(struct list_head * x, \state enter, \state exit) =
	\at(enter, dllprev(x)) == \at(exit, dllprev(x))
;)
_(logic _(dryad "same:dllprev_R") \bool same_dllprev_reach(struct list_head * x, \state enter, \state exit) = 
	\at(enter, dllprev_reach(x)) == \at(exit, dllprev_reach(x)) 
;)


_(logic \bool same_dllnext_all(struct list_head * x, \state enter, \state exit) = 
	same_dllnext(x, enter, exit) 
	&& same_dllnext_reach(x, enter, exit)
;)

// ------------------------------------------------------------------------------------------------------
_(logic _(dryad "cond:dllnext") \bool cond_same_dllnext(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dllnext_reach(y)))) ==> \at(enter, dllnext(y)) == \at(exit, dllnext(y))
;)
_(logic _(dryad "cond:dllnext_R") \bool cond_same_dllnext_reach(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dllnext_reach(y)))) ==> \at(enter, dllnext_reach(y)) == \at(exit, dllnext_reach(y))
;)

_(logic _(dryad "cond:dllprev") \bool cond_same_dllprev(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev(y)) == \at(exit, dllprev(y))
;)
_(logic _(dryad "cond:dllprev_R") \bool cond_same_dllprev_reach(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	(! \oset_in(x, \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev_reach(y)) == \at(exit, dllprev_reach(y))
;)

_(logic \bool cond_same_dllnext_all(struct list_head * x, struct list_head * y, \state enter, \state exit) =
	cond_same_dllnext(x, y, enter, exit) 
	&& cond_same_dllnext_reach(x, y, enter, exit)
;)

// ------------------------------------------------------------------------------------------------------
_(logic _(dryad "disj:dllnext") \bool disj_same_dllnext(\oset heaplet, struct list_head * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, dllnext_reach(y)))) ==> \at(enter, dllnext(y)) == \at(exit, dllnext(y))
;)
_(logic _(dryad "disj:dllnext_R") \bool disj_same_dllnext_reach(\oset heaplet, struct list_head * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, dllnext_reach(y)))) ==> \at(enter, dllnext_reach(y)) == \at(exit, dllnext_reach(y))
;)

_(logic _(dryad "disj:dllprev") \bool disj_same_dllprev(\oset heaplet, struct list_head * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev(y)) == \at(exit, dllprev(y))
;)
_(logic _(dryad "disj:dllprev_R") \bool disj_same_dllprev_reach(\oset heaplet, struct list_head * y, \state enter, \state exit) =
	(\oset_disjoint(\at(enter, heaplet), \at(enter, dllprev_reach(y)))) ==> \at(enter, dllprev_reach(y)) == \at(exit, dllprev_reach(y))
;)

_(logic \bool disj_same_dllnext_all(\oset heaplet, struct list_head * y, \state enter, \state exit) =
	disj_same_dllnext(\at(enter, heaplet), y, enter, exit) 
	&& disj_same_dllnext_reach(\at(enter, heaplet), y, enter, exit)
;)




// dummy function denoting the end of dl_node defs
_(abstract _(dryad "end") void end_slave_dl_node_defs(struct list_head * x) ;)
// ---------------------------------------------------------------------------------------------------------

#endif
