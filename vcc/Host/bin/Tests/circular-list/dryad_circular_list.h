#ifndef DRYAD_CIRC_DEFS_H
#define DRYAD_CIRC_DEFS_H

#include <vcc.h>
#include <stdlib.h>

typedef 
_(dryad "lseg:lseg_R")
struct c_node {
	struct c_node * next;
} CNode;


_(pure _(dryad "base:lseg")  \bool lseg(struct c_node * hd, struct c_node * tl)
  _(reads \universe())
//  _(ensures hd == tl ==> (\result && (lseg_reach(hd, tl) == \oset_empty())))
  ;)

_(pure _(dryad "base:lseg_R")  \oset lseg_reach(struct c_node * hd, struct c_node * tl)
	_(reads \universe())
//	_(ensures hd == tl  ==> \result == \oset_empty())
//	_(ensures (hd != NULL && hd != tl)  ==> \oset_in(hd, \result))
;)

// ----------------------------------------------------------------------------------------------------------------------------
_(logic _(dryad "unfold:lseg")  \bool unfold_lseg(struct c_node * hd, struct c_node * tl) =
    (hd == tl ==> (lseg(hd, tl) && lseg_reach(hd, tl) == \oset_empty())) &&
    (hd != tl ==> (lseg(hd, tl) <==> (lseg(hd->next,tl) && (! \oset_in(hd, lseg_reach(hd->next,tl))) ) ))
;)
_(logic _(dryad "unfold:lseg_R")  \bool unfold_lseg_reach(struct c_node * hd, struct c_node * tl) =
  (hd == tl ==> lseg_reach(hd, tl) == \oset_empty()) &&
	(hd != tl ==> (lseg_reach(hd, tl) == \oset_union(lseg_reach(hd->next, tl), \oset_singleton(hd))) ) 
;)

_(abstract  \bool unfold_all_bin(struct c_node * hd, struct c_node *  tl)
  _(reads \universe())
  _(ensures unfold_lseg(hd, tl))
  _(ensures unfold_lseg_reach(hd, tl))
;)
// -----------------------------------------------------------------------------------------------------
_(logic  _(dryad "same:lseg") 
  \bool same_lseg(struct c_node * hd, struct c_node * tl, \state enter, \state exit) =
    \at(enter, lseg(hd, tl)) == \at(exit, lseg(hd, tl)) ;)

_(logic  _(dryad "same:lseg_R") 
  \bool same_lseg_reach(struct c_node * hd, struct c_node * tl, \state enter, \state exit) =
    \at(enter, lseg_reach(hd, tl)) == \at(exit, lseg_reach(hd, tl)) ;)

_(logic  \bool same_all_bin(struct c_node * hd, struct c_node * tl, \state enter, \state exit) = 
	same_lseg(hd, tl, enter, exit) 
	&& same_lseg_reach(hd, tl, enter, exit)
;)


// ------------------------------------------------------------------------------------------------------
_(logic _(dryad "cond:lseg") 
  \bool disj_same_lseg(struct c_node * x, struct c_node * hd, struct c_node * tl, 
                      \state enter, \state exit) = 
    (!(\oset_in(x, \at(enter, lseg_reach(hd, tl)))) ==> 
      \at(enter, lseg(hd, tl)) == \at(exit, lseg(hd, tl)) ) ;)
_(logic  _(dryad "cond:lseg_R") 
  \bool disj_same_lseg_reach(struct c_node * x, struct c_node * hd, struct c_node * tl, 
                            \state enter, \state exit) = 
    (!(\oset_in(x, \at(enter, lseg_reach(hd, tl)))) ==> 
      \at(enter, lseg_reach(hd, tl)) == \at(exit, lseg_reach(hd, tl)) ) ;)
_(logic  
  \bool disj_same_all_bin(\oset heaplet, struct c_node * hd, struct c_node * tl, \state enter, \state exit) =
       disj_same_lseg(\at(enter, heaplet), hd, tl, enter, exit) 
  	&& disj_same_lseg_reach(\at(enter, heaplet), hd, tl, enter, exit) 
;)
// ------------------------------------------------------------------------------------------------------
_(logic _(dryad "disj:lseg") 
  \bool disj_same_lseg(\oset heaplet, struct c_node * hd, struct c_node * tl, 
                      \state enter, \state exit) = 
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, lseg_reach(hd, tl)))) ==> 
      \at(enter, lseg(hd, tl)) == \at(exit, lseg(hd, tl)) ) ;)
_(logic  _(dryad "disj:lseg_R") 
  \bool disj_same_lseg_reach(\oset heaplet, struct c_node * hd, struct c_node * tl, 
                            \state enter, \state exit) = 
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, lseg_reach(hd, tl)))) ==> 
      \at(enter, lseg_reach(hd, tl)) == \at(exit, lseg_reach(hd, tl)) ) ;)
_(logic  
  \bool disj_same_all_bin(\oset heaplet, struct c_node * hd, struct c_node * tl, \state enter, \state exit) =
       disj_same_lseg(\at(enter, heaplet), hd, tl, enter, exit) 
  	&& disj_same_lseg_reach(\at(enter, heaplet), hd, tl, enter, exit) 
;)
// ------------------------------------------------------------------------------------------------------


// dummy function denoting the end of sll node defs
_(abstract _(dryad "end") void end_c_node_defs(struct c_node * x) ;)
// ---------------------------------------------------------------------------------------------------------
#endif
