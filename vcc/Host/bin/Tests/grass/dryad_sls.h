#ifndef DRYAD_SRTL_DEFS_H
#define DRYAD_SRTL_DEFS_H

#include <vcc.h>
// ------------------------
#include <stdlib.h>
//#include "intset_defs.h"
//#include "intbag_defs.h"

typedef
_(dryad "sll:srtl:rsrtl:sll_R:srtl_R:rsrtl_R:keys:llen_next:lseg:slseg:lseg_R:slseg_R:lseg_keys:lseg_len_next")
struct s_node {
  int key;
  struct s_node * next;
} Node;


_(abstract _(dryad "base:sll") \bool sll(struct s_node * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
;)
_(abstract _(dryad "base:srtl") \bool srtl(struct s_node * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
;)
_(abstract _(dryad "base:rsrtl") \bool rsrtl(struct s_node * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
;)


_(abstract _(dryad "base:sll_R") \oset sll_reach(struct s_node * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
			&& ((hd == NULL) ==> (\result == \oset_empty())))
;)
_(abstract _(dryad "base:srtl_R") \oset srtl_reach(struct s_node * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
			&& ((hd == NULL) ==> (\result == \oset_empty())))
;)
_(abstract _(dryad "base:rsrtl_R") \oset rsrtl_reach(struct s_node * hd)
	_(reads \universe())
	_(ensures ((hd != NULL) ==> \oset_in(hd, \result))
			&& ((hd == NULL) ==> (\result == \oset_empty())))
;)

_(abstract _(dryad "base:keys") \intset sll_keys(struct s_node * hd) // [key]
	_(reads \universe())
	_(ensures (hd != NULL ==> \intset_in(hd->key, \result)))
	_(ensures (hd == NULL ==> (\result == \intset_empty())))
	;)

_(abstract _(dryad "base:llen_next") \natural sll_list_len_next(struct s_node * x)
  _(reads \universe())
  _(ensures x != NULL ==> \result > 0)
  _(ensures x == NULL ==> \result == 0)
  ;)

_(abstract _(dryad "base:lseg") \bool sll_lseg(struct s_node * hd, struct s_node * tl)
  _(reads \universe())
  _(ensures (hd == NULL && hd != tl) ==> \result)
  _(ensures hd == tl ==> \result)
  _(ensures tl == NULL ==> (\result == sll(hd)))
  _(ensures (sll(tl) && \oset_disjoint(sll_reach(tl), sll_lseg_reach(hd, tl))) ==>
             (sll(hd)
              && sll_reach(hd) == \oset_union(sll_lseg_reach(hd, tl), sll_reach(tl)) 
						  && (sll_keys(hd) == \intset_union(sll_keys(tl), sll_lseg_keys(hd, tl)))
//						  && _dryad_keyb(hd) == \intbag_union(_dryad_keyb(tl), _dryad_lsegb(hd, tl))
						 ) ) 
  _(ensures (tl != NULL && sll(tl->next) && sll_lseg(hd, tl)
         && \oset_disjoint(sll_reach(tl->next), sll_lseg_reach(hd, tl)) 
		     && (! \oset_in(tl, sll_reach(tl->next)) ) 
		     && (! \oset_in(tl, sll_lseg_reach(hd, tl)))   ) ==>
                   (sll_lseg (hd, tl->next) 
				   && (sll_lseg_keys(hd, tl->next) == \intset_union(\intset_singleton(tl->key), sll_lseg_keys(hd, tl))) 
//				   && _dryad_lsegb(hd, tl->next) == \intbag_union(\intbag_singleton(tl->key), _dryad_lsegb(hd, tl))
				   && (sll_lseg_reach(hd, tl->next) == (\oset_union(\oset_singleton(tl), sll_lseg_reach(hd, tl))))   ) ) 
  ;)

_(abstract _(dryad "base:slseg") \bool srtl_lseg(struct s_node * hd, struct s_node * tl)
  _(reads \universe())
  _(ensures (hd == NULL && hd != tl) ==> \result)
  _(ensures hd == tl ==> \result)
  _(ensures tl == NULL ==> (\result == srtl(hd)))
  _(ensures (srtl(tl) && \oset_disjoint(srtl_reach(tl), srtl_lseg_reach(hd, tl))) ==>
             (srtl(hd) 
              && srtl_reach(hd) == \oset_union(srtl_lseg_reach(hd, tl), srtl_reach(tl))
						  && (sll_keys(hd) == \intset_union(sll_keys(tl), sll_lseg_keys(hd, tl)))
//						  && _dryad_keyb(hd) == \intbag_union(_dryad_keyb(tl), _dryad_lsegb(hd, tl))
						 ) ) 
  _(ensures (tl != NULL && srtl(tl->next) && srtl_lseg(hd, tl)
         && \oset_disjoint(srtl_reach(tl->next), srtl_lseg_reach(hd, tl)) 
		     && (! \oset_in(tl, srtl_reach(tl->next)) ) 
		     && (! \oset_in(tl, srtl_lseg_reach(hd, tl)))   
         && \intset_le(\intset_singleton(tl->key), sll_keys(tl->next) ) ) ==>
         ( srtl_lseg (hd, tl->next) 
				   && (sll_lseg_keys(hd, tl->next) == \intset_union(\intset_singleton(tl->key), sll_lseg_keys(hd, tl)))
//				   && _dryad_lsegb(hd, tl->next) == \intbag_union(\intbag_singleton(tl->key), _dryad_lsegb(hd, tl))
				   && (srtl_lseg_reach(hd, tl->next) == \oset_union(\oset_singleton(tl), srtl_lseg_reach(hd, tl)))   ) )
  ;)

_(abstract _(dryad "base:lseg_R") \oset sll_lseg_reach(struct s_node * hd, struct s_node * tl)
	_(reads \universe())
	_(ensures hd == NULL ==> (\result == \oset_empty()))
	_(ensures hd == tl ==> (\result == \oset_empty()))
	_(ensures (hd != NULL && hd != tl) ==> \oset_in(hd, \result))
	_(ensures (hd != NULL && tl == NULL) ==> (\result == sll_reach(hd)))
;)
_(abstract _(dryad "base:slseg_R") \oset srtl_lseg_reach(struct s_node * hd, struct s_node * tl)
	_(reads \universe())
	_(ensures (hd == NULL && hd != tl) ==> (\result == \oset_empty()))
	_(ensures hd == tl ==>   (\result == \oset_empty()))
	_(ensures (hd != NULL && hd != tl) ==> \oset_in(hd, \result))
	_(ensures (tl == NULL) ==> (\result == srtl_reach(hd)))
;)

_(abstract _(dryad "base:lseg_keys") \intset sll_lseg_keys(struct s_node * hd, struct s_node * tl)
  _(reads \universe())
  _(ensures (hd == NULL && hd != tl) ==> (\result == \intset_empty()))
  _(ensures hd == tl   ==> (\result == \intset_empty()))
  _(ensures (hd != NULL && hd != tl)   ==> \intset_in(hd->key, \result))
  _(ensures (tl == NULL) ==> (\result == sll_keys(hd)))
;)

_(abstract _(dryad "base:lseg_len_next") \natural sll_lseg_len_next(struct s_node * hd, struct s_node * tl)
  _(reads \universe())
  _(ensures hd == tl   ==> \result == 0)
  _(ensures (hd == NULL && hd != tl) ==> \result == 0)
  _(ensures (hd != NULL && hd != tl)   ==> \result > 0)
  _(ensures (hd != NULL && tl == NULL) ==> \result == sll_lseg_len_next(hd, tl))
;)

// ----------------------------------------------------------------------------------------------------------------------------
_(logic _(dryad "unfold:sll") \bool unfold_sll(struct s_node * hd) =
	(hd != NULL ==>
		(sll(hd) <==> 
			(sll(hd->next) && 
			(! \oset_in(hd, sll_reach(hd->next))) ) )  )
;)
_(logic _(dryad "unfold:srtl") \bool unfold_srtl(struct s_node * hd) =
	(hd != NULL ==>
		(srtl(hd) <==> 
			(srtl(hd->next) 
        && (! \oset_in(hd, srtl_reach(hd->next)))
        &&    \intset_le_one1(hd->key, sll_keys(hd->next)) ) ) ) 
;)
_(logic _(dryad "unfold:rsrtl") \bool unfold_rsrtl(struct s_node * hd) =
	(hd != NULL ==>
		(rsrtl(hd) <==> 
			(rsrtl(hd->next) 
        && !(\oset_in(hd, rsrtl_reach(hd->next)))
        && \intset_le_one2(sll_keys(hd->next), hd->key) ) ) ) 
;)

_(logic _(dryad "unfold:sll_R") \bool unfold_sll_reach(struct s_node * hd) =
	(hd != NULL ==>
		(sll_reach(hd) == \oset_union(sll_reach(hd->next), \oset_singleton(hd))) ) 
	;)
_(logic _(dryad "unfold:srtl_R") \bool unfold_srtl_reach(struct s_node * hd) =
	(hd != NULL ==>
		(srtl_reach(hd) == \oset_union(srtl_reach(hd->next), \oset_singleton(hd))) ) 
;)
_(logic _(dryad "unfold:rsrtl_R") \bool unfold_rsrtl_reach(struct s_node * hd) =
	(hd != NULL ==>
		(rsrtl_reach(hd) == \oset_union(rsrtl_reach(hd->next), \oset_singleton(hd))) ) 
;)

_(logic _(dryad "unfold:keys") \bool unfold_sll_keys(struct s_node * hd) =
		(hd != NULL ==> (sll_keys(hd) == (\intset_union(sll_keys(hd->next), \intset_singleton(hd->key)))))
;)

_(logic _(dryad "unfold:llen_next") \bool unfold_sll_list_len_next(struct s_node * hd) =
    (hd != NULL ==> (sll_list_len_next(hd) == sll_list_len_next(hd->next) + 1))  
;)

_(logic \bool unfold_sll_all_un(struct s_node * x) =
  unfold_sll(x)
  && unfold_sll_reach(x)
	&& unfold_sll_keys(x)
  && unfold_sll_list_len_next(x)
;)
_(logic \bool unfold_srtl_all_un(struct s_node * x) =
  unfold_srtl(x)
	&& unfold_srtl_reach(x)
	&& unfold_sll_keys(x)
  && unfold_sll_list_len_next(x)
;)


_(logic _(dryad "unfold:lseg") \bool unfold_sll_lseg(struct s_node * hd, struct s_node * tl) =
  ((hd != NULL && hd != tl) ==>
      (sll_lseg(hd,tl) <==> 
        (sll_lseg(hd->next,tl) && (! \oset_in(hd, sll_lseg_reach(hd->next,tl))) ) ) )
;)
_(logic _(dryad "unfold:slseg") \bool unfold_srtl_lseg(struct s_node * hd, struct s_node * tl) =
  ((hd != NULL && hd != tl) ==>
      (srtl_lseg(hd,tl) <==> 
        (srtl_lseg(hd->next,tl) 
        && (! \oset_in(hd, srtl_lseg_reach(hd->next,tl))) 
        && \intset_le_one1(hd->key, sll_lseg_keys(hd->next, tl)) ) ) )
  ;)

_(logic _(dryad "unfold:lseg_R") \bool unfold_sll_lseg_reach(struct s_node * hd, struct s_node * tl) =
	((hd != NULL && hd != tl) ==> 
       (sll_lseg_reach(hd, tl) == \oset_union(sll_lseg_reach(hd->next, tl), \oset_singleton(hd))) ) 
;)
_(logic _(dryad "unfold:slseg_R") \bool unfold_srtl_lseg_reach(struct s_node * hd, struct s_node * tl) =
  ((hd != NULL && hd != tl) ==> 
       ((srtl_lseg_reach(hd, tl) == \oset_union(srtl_lseg_reach(hd->next, tl), \oset_singleton(hd))) ) )
 ;)

_(logic _(dryad "unfold:lseg_keys") \bool unfold_sll_lseg_keys(struct s_node * hd, struct s_node * tl) =
      ((hd != NULL && hd != tl) ==> (sll_lseg_keys(hd, tl) ==
          \intset_union(sll_lseg_keys(hd->next, tl), \intset_singleton(hd->key)) ) )
;)

_(logic _(dryad "unfold:lseg_len_next") \bool unfold_sll_lseg_len_next(struct s_node * hd, struct s_node * tl) =
      ((hd != NULL && hd != tl) ==> (sll_lseg_len_next(hd, tl) == (sll_lseg_len_next(hd->next, tl) + 1)))  ;)

_(logic \bool unfold_sll_all_bin(struct s_node * hd, struct s_node *  tl) =
  unfold_sll_lseg(hd, tl)
  && unfold_sll_lseg_reach(hd, tl)
  && unfold_sll_lseg_keys(hd, tl)
  && unfold_sll_lseg_len_next(hd, tl)
;)
_(logic \bool unfold_srtl_all_bin(struct s_node * hd, struct s_node *  tl) =
  unfold_srtl_lseg(hd, tl)
  && unfold_srtl_lseg_reach(hd, tl)
  && unfold_sll_lseg_keys(hd, tl)
  && unfold_sll_lseg_len_next(hd, tl)
;)

// ----------------------------------------------------------------------------------------------------------------------------

// axioms needed to complete the proof
//_(axiom \forall \objset os1, os2; \disjoint(os1, os2) <==> \subset(os1, (\universe() \diff os2)))
//_(axiom \forall \objset os1, os2; \forall \object o; (os1 == (os2 \union {o})) ==> \subset(os2, os1)) // [sll-reverse]

// -----------------------------------------------------------------------------------------------------
_(logic _(dryad "same:sll") \bool same_sll(struct s_node * x, \state enter, \state exit) =
	\at(enter, sll(x)) == \at(exit, sll(x))
;)
_(logic _(dryad "same:srtl") \bool same_srtl(struct s_node * x, \state enter, \state exit) =
	\at(enter, srtl(x)) == \at(exit, srtl(x))
;)
_(logic _(dryad "same:rsrtl") \bool same_rsrtl(struct s_node * x, \state enter, \state exit) =
	\at(enter, rsrtl(x)) == \at(exit, rsrtl(x))
;)
_(logic _(dryad "same:sll_R") \bool same_sll_reach(struct s_node * x, \state enter, \state exit) = 
	(\at(enter, sll_reach(x)) == \at(exit, sll_reach(x))) 
;)
_(logic _(dryad "same:srtl_R") \bool same_srtl_reach(struct s_node * x, \state enter, \state exit) = 
	(\at(enter, srtl_reach(x)) == \at(exit, srtl_reach(x)))
;)
_(logic _(dryad "same:rsrtl_R") \bool same_rsrtl_reach(struct s_node * x, \state enter, \state exit) = 
	(\at(enter, rsrtl_reach(x)) == \at(exit, rsrtl_reach(x)))
;)
_(logic _(dryad "same:keys") \bool same_sll_keys(struct s_node * x, \state enter, \state exit) =
	(\at(enter, sll_keys(x)) == \at(exit, sll_keys(x)))
;)
_(logic _(dryad "same:llen_next") \bool same_sll_list_len_next(struct s_node * x, \state enter, \state exit) =
	\at(enter, sll_list_len_next(x)) == \at(exit, sll_list_len_next(x))
;)
_(logic \bool same_sll_all_un(struct s_node * x, \state enter, \state exit) = 
	same_sll(x, enter, exit) 
	&& same_sll_reach(x, enter, exit)
	&& same_sll_keys(x, enter, exit)
	&& same_sll_list_len_next(x, enter, exit)
;)
_(logic \bool same_srtl_all_un(struct s_node * x, \state enter, \state exit) = 
	same_srtl(x, enter, exit) 
	&& same_srtl_reach(x, enter, exit)
	&& same_sll_keys(x, enter, exit)
	&& same_sll_list_len_next(x, enter, exit)
;)

_(logic _(dryad "same:lseg") 
  \bool same_sll_lseg(struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
    \at(enter, sll_lseg(hd, tl)) == \at(exit, sll_lseg(hd, tl)) ;)
_(logic _(dryad "same:slseg") 
  \bool same_srtl_lseg(struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
    \at(enter, srtl_lseg(hd, tl)) == \at(exit, srtl_lseg(hd, tl)) ;)

_(logic _(dryad "same:lseg_R") 
  \bool same_sll_lseg_reach(struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
    (\at(enter, sll_lseg_reach(hd, tl)) == \at(exit, sll_lseg_reach(hd, tl))) ;)
_(logic _(dryad "same:slseg_R") 
  \bool same_srtl_lseg_reach(struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
    (\at(enter, srtl_lseg_reach(hd, tl) == \at(exit, srtl_lseg_reach(hd, tl)))) ;)

_(logic _(dryad "same:lseg_keys")
  \bool same_sll_lseg_keys(struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
    (\at(enter, sll_lseg_keys(hd, tl)) == \at(exit, sll_lseg_keys(hd, tl))) ;)
_(logic _(dryad "same:lseg_len_next")
  \bool same_sll_lseg_len_next(struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
    \at(enter, sll_lseg_len_next(hd, tl)) == \at(exit, sll_lseg_len_next(hd, tl)) ;)

_(logic \bool same_sll_all_bin(struct s_node * hd, struct s_node * tl, \state enter, \state exit) = 
	same_sll_lseg(hd, tl, enter, exit) 
	&& same_sll_lseg_reach(hd, tl, enter, exit)
	&& same_sll_lseg_keys(hd, tl, enter, exit)
	&& same_sll_lseg_len_next(hd, tl, enter, exit)
;)
_(logic \bool same_srtl_all_bin(struct s_node * hd, struct s_node * tl, \state enter, \state exit) = 
	same_srtl_lseg(hd, tl, enter, exit) 
	&& same_srtl_lseg_reach(hd, tl, enter, exit)
	&& same_sll_lseg_keys(hd, tl, enter, exit)
	&& same_sll_lseg_len_next(hd, tl, enter, exit)
;)


// ------------------------------------------------------------------------------------------------------
_(logic _(dryad "cond:sll") 
  \bool cond_same_sll(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, sll_reach(y)))) ==> \at(enter, sll(y)) == \at(exit, sll(y)) ;)
_(logic _(dryad "cond:srtl") 
  \bool cond_same_srtl(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, srtl_reach(y)))) ==> \at(enter, srtl(y)) == \at(exit, srtl(y)) ;)
_(logic _(dryad "cond:rsrtl") 
  \bool cond_same_rsrtl(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, rsrtl_reach(y)))) ==> \at(enter, rsrtl(y)) == \at(exit, rsrtl(y)) ;)

_(logic _(dryad "cond:sll_R") 
  \bool cond_same_sll_reach(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, sll_reach(y)))) ==> (\at(enter, sll_reach(y)) == \at(exit, sll_reach(y))) ;)
_(logic _(dryad "cond:srtl_R") 
  \bool cond_same_srtl_reach(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, srtl_reach(y)))) ==> (\at(enter, srtl_reach(y)) == \at(exit, srtl_reach(y))) ;)
_(logic _(dryad "cond:rsrtl_R") 
  \bool cond_same_rsrtl_reach(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, rsrtl_reach(y)))) ==> (\at(enter, rsrtl_reach(y)) == \at(exit, rsrtl_reach(y))) ;)

_(logic _(dryad "cond:keys") 
  \bool cond_same_sll_keys(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, sll_reach(y)))) ==> (\at(enter, sll_keys(y)) == \at(exit, sll_keys(y))) ;)
_(logic _(dryad "cond:llen_next") 
  \bool cond_same_sll_list_len_next(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	  (! \oset_in(x, \at(enter, sll_reach(y)))) ==> \at(enter, sll_list_len_next(y)) == \at(exit, sll_list_len_next(y))
;)

_(logic
  \bool cond_same_sll_all_un(struct s_node * x, struct s_node * y, \state enter, \state exit) =
  	cond_same_sll(x, y, enter, exit) 
  	&& cond_same_sll_reach(x, y, enter, exit)
  	&& cond_same_sll_keys(x, y, enter, exit) 
  	&& cond_same_sll_list_len_next(x, y, enter, exit) ;)
_(logic
  \bool cond_same_srtl_all_un(struct s_node * x, struct s_node * y, \state enter, \state exit) =
  	cond_same_srtl(x, y, enter, exit) 
  	&& cond_same_srtl_reach(x, y, enter, exit)
  	&& cond_same_sll_keys(x, y, enter, exit) 
  	&& cond_same_sll_list_len_next(x, y, enter, exit) ;)

_(logic _(dryad "cond:lseg") 
  \bool cond_same_sll_lseg(struct s_node * x, struct s_node * hd, struct s_node * tl, 
                      \state enter, \state exit) = 
    ((! \oset_in(x, \at(enter, sll_lseg_reach(hd, tl)))) ==> 
      \at(enter, sll_lseg(hd, tl)) == \at(exit, sll_lseg(hd, tl)) ) ;)
_(logic _(dryad "cond:slseg") 
  \bool cond_same_srtl_lseg(struct s_node * x, struct s_node * hd, struct s_node * tl, 
                      \state enter, \state exit) = 
    ((! \oset_in(x, \at(enter, srtl_lseg_reach(hd, tl)))) ==> 
      \at(enter, srtl_lseg(hd, tl)) == \at(exit, srtl_lseg(hd, tl)) ) ;)

_(logic _(dryad "cond:lseg_R") 
  \bool cond_same_sll_lseg_reach(struct s_node * x, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) = 
    ((! \oset_in(x, \at(enter, sll_lseg_reach(hd, tl)))) ==> 
      (\at(enter, sll_lseg_reach(hd, tl)) == \at(exit, sll_lseg_reach(hd, tl)) )) ;)
_(logic _(dryad "cond:slseg_R") 
  \bool cond_same_srtl_lseg_reach(struct s_node * x, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) = 
    ((! \oset_in(x, \at(enter, srtl_lseg_reach(hd, tl)))) ==> 
        (\at(enter, srtl_lseg_reach(hd, tl)) == \at(exit, srtl_lseg_reach(hd, tl)) )) ;)

_(logic _(dryad "cond:lseg_keys")
  \bool cond_same_sll_lseg_keys(struct s_node * x, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) =
    ((! \oset_in(x, \at(enter, sll_lseg_reach(hd, tl)))) ==>
      (\at(enter, sll_lseg_keys(hd, tl)) == \at(exit, sll_lseg_keys(hd, tl)))) ;)
_(logic _(dryad "cond:lseg_len_next")
  \bool cond_same_sll_lseg_len_next(struct s_node * x, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) =
    ((! \oset_in(x, \at(enter, sll_lseg_reach(hd, tl)))) ==>
      \at(enter, sll_lseg_len_next(hd, tl)) == \at(exit, sll_lseg_len_next(hd, tl))) ;)

_(logic 
  \bool cond_same_sll_all_bin(struct s_node * x, struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
	  cond_same_sll_lseg(x, hd, tl, enter, exit) 
  	&& cond_same_sll_lseg_reach(x, hd, tl, enter, exit)
  	&& cond_same_sll_lseg_keys(x, hd, tl, enter, exit)
  	&& cond_same_sll_lseg_len_next(x, hd, tl, enter, exit)
;)
_(logic 
  \bool cond_same_srtl_all_bin(struct s_node * x, struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
	  cond_same_srtl_lseg(x, hd, tl, enter, exit) 
  	&& cond_same_srtl_lseg_reach(x, hd, tl, enter, exit)
  	&& cond_same_sll_lseg_keys(x, hd, tl, enter, exit)
  	&& cond_same_sll_lseg_len_next(x, hd, tl, enter, exit)
;)


// -------- disjoint -------------------------------------------------------------------------
_(logic _(dryad "disj:sll") 
  \bool disj_same_sll(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, sll_reach(y)))) ==> \at(enter, sll(y)) == \at(exit, sll(y)) ;)
_(logic _(dryad "disj:srtl") 
  \bool disj_same_srtl(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, srtl_reach(y)))) ==> \at(enter, srtl(y)) == \at(exit, srtl(y)) ;)
_(logic _(dryad "disj:rsrtl") 
  \bool disj_same_rsrtl(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, rsrtl_reach(y)))) ==> \at(enter, rsrtl(y)) == \at(exit, rsrtl(y)) ;)

_(logic _(dryad "disj:sll_R") 
  \bool disj_same_sll_reach(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, sll_reach(y)))) ==> (\at(enter, sll_reach(y)) == \at(exit, sll_reach(y))) ;)
_(logic _(dryad "disj:srtl_R") 
  \bool disj_same_srtl_reach(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, srtl_reach(y)))) ==> (\at(enter, srtl_reach(y)) == \at(exit, srtl_reach(y))) ;)
_(logic _(dryad "disj:rsrtl_R") 
  \bool disj_same_rsrtl_reach(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, rsrtl_reach(y)))) ==> (\at(enter, rsrtl_reach(y)) == \at(exit, rsrtl_reach(y))) ;)

_(logic _(dryad "disj:keys") 
  \bool disj_same_sll_keys(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, sll_reach(y)))) ==> (\at(enter, sll_keys(y)) == \at(exit, sll_keys(y))) ;)
_(logic _(dryad "disj:llen_next") 
  \bool disj_same_sll_list_len_next(\oset heaplet, struct s_node * y, \state enter, \state exit) =
	  (\oset_disjoint(\at(enter, heaplet), \at(enter, sll_reach(y)))) ==> \at(enter, sll_list_len_next(y)) == \at(exit, sll_list_len_next(y))
;)

_(logic
  \bool disj_same_sll_all_un(\oset heaplet, struct s_node * y, \state enter, \state exit) =
  	disj_same_sll(\at(enter, heaplet), y, enter, exit) 
  	&& disj_same_sll_reach(\at(enter, heaplet), y, enter, exit)
  	&& disj_same_sll_keys(\at(enter, heaplet), y, enter, exit) 
  	&& disj_same_sll_list_len_next(\at(enter, heaplet), y, enter, exit) ;)
_(logic
  \bool disj_same_srtl_all_un(\oset heaplet, struct s_node * y, \state enter, \state exit) =
  	disj_same_srtl(\at(enter, heaplet), y, enter, exit) 
  	&& disj_same_srtl_reach(\at(enter, heaplet), y, enter, exit)
  	&& disj_same_sll_keys(\at(enter, heaplet), y, enter, exit) 
  	&& disj_same_sll_list_len_next(\at(enter, heaplet), y, enter, exit) ;)

_(logic _(dryad "disj:lseg") 
  \bool disj_same_sll_lseg(\oset heaplet, struct s_node * hd, struct s_node * tl, 
                      \state enter, \state exit) = 
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, sll_lseg_reach(hd, tl)))) ==> 
      \at(enter, sll_lseg(hd, tl)) == \at(exit, sll_lseg(hd, tl)) ) ;)
_(logic _(dryad "disj:slseg") 
  \bool disj_same_srtl_lseg(\oset heaplet, struct s_node * hd, struct s_node * tl, 
                      \state enter, \state exit) = 
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, srtl_lseg_reach(hd, tl)))) ==> 
      \at(enter, srtl_lseg(hd, tl)) == \at(exit, srtl_lseg(hd, tl)) ) ;)

_(logic _(dryad "disj:lseg_R") 
  \bool disj_same_sll_lseg_reach(\oset heaplet, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) = 
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, sll_lseg_reach(hd, tl)))) ==> 
      (\at(enter, sll_lseg_reach(hd, tl)) == \at(exit, sll_lseg_reach(hd, tl)) )) ;)
_(logic _(dryad "disj:slseg_R") 
  \bool disj_same_srtl_lseg_reach(\oset heaplet, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) = 
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, srtl_lseg_reach(hd, tl)))) ==> 
        (\at(enter, srtl_lseg_reach(hd, tl)) == \at(exit, srtl_lseg_reach(hd, tl)) )) ;)

_(logic _(dryad "disj:lseg_keys")
  \bool disj_same_sll_lseg_keys(\oset heaplet, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) =
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, sll_lseg_reach(hd, tl)))) ==>
      (\at(enter, sll_lseg_keys(hd, tl)) == \at(exit, sll_lseg_keys(hd, tl)))) ;)
_(logic _(dryad "disj:lseg_len_next")
  \bool disj_same_sll_lseg_len_next(\oset heaplet, struct s_node * hd, struct s_node * tl, 
                            \state enter, \state exit) =
    ((\oset_disjoint(\at(enter, heaplet), \at(enter, sll_lseg_reach(hd, tl)))) ==>
      \at(enter, sll_lseg_len_next(hd, tl)) == \at(exit, sll_lseg_len_next(hd, tl))) ;)

_(logic 
  \bool disj_same_sll_all_bin(\oset heaplet, struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
	  disj_same_sll_lseg(\at(enter, heaplet), hd, tl, enter, exit) 
  	&& disj_same_sll_lseg_reach(\at(enter, heaplet), hd, tl, enter, exit)
  	&& disj_same_sll_lseg_keys(\at(enter, heaplet), hd, tl, enter, exit)
  	&& disj_same_sll_lseg_len_next(\at(enter, heaplet), hd, tl, enter, exit)
;)
_(logic 
  \bool disj_same_srtl_all_bin(\oset heaplet, struct s_node * hd, struct s_node * tl, \state enter, \state exit) =
	  disj_same_srtl_lseg(\at(enter, heaplet), hd, tl, enter, exit) 
  	&& disj_same_srtl_lseg_reach(\at(enter, heaplet), hd, tl, enter, exit)
  	&& disj_same_sll_lseg_keys(\at(enter, heaplet), hd, tl, enter, exit)
  	&& disj_same_sll_lseg_len_next(\at(enter, heaplet), hd, tl, enter, exit)
;)

/*
_(def _(dryad "lemma:patch")
  void sll_lemma_patch(struct s_node * b, struct s_node * e)
    _(ensures (sll(b) && sll(e) && sll_lseg(b, e)) ==> 
            (sll_reach(b) == sll_lseg_reach(b, e) \union sll_reach(e))
         && (sll_list_len_next(b) == (sll_lseg_len_next(b, e) + sll_list_len_next(e))))
    _(decreases sll_list_len_next(b))
  {
    if (b == e) { 
      return;
    }else  {
      _(assume unfold_sll_all_un(b))
      _(assume unfold_sll_all_bin(b, e))
      sll_lemma_patch(b->next, e);
    }
  } ;)
_(def _(dryad "lemma:patch_sorted")
  void srtl_lemma_patch(struct s_node * b, struct s_node * e)
    _(ensures (srtl(b) && srtl(e) && srtl_lseg(b, e)) ==> 
            (srtl_reach(b) == srtl_lseg_reach(b, e) \union srtl_reach(e))
         && (sll_list_len_next(b) == (sll_lseg_len_next(b, e) + sll_list_len_next(e))))
    _(decreases sll_list_len_next(b))
  {
    if (b == e) { 
      return;
    }else  {
      _(assume unfold_srtl_all_un(b))
      _(assume unfold_srtl_all_bin(b, e))
      srtl_lemma_patch(b->next, e);
    }
  } ;)
*/
_(axiom \forall struct s_node * x; srtl(x) ==> sll(x))
_(axiom \forall struct s_node * x; rsrtl(x) ==> sll(x))
_(axiom \forall struct s_node * x; sll_reach(x) == srtl_reach(x))
_(axiom \forall struct s_node * x; srtl_reach(x) == rsrtl_reach(x))
_(axiom \forall struct s_node * x,y; sll_lseg_reach(x, y) == srtl_lseg_reach(x, y))

// dummy function denoting the end of sll s_node defs
_(abstract _(dryad "end") void end_dl_s_node_defs(struct s_node * x) ;)

_(logic \bool mutable_list(struct s_node * x) =  x != NULL ==> \mutable(x) && \writable(x))

_(logic \bool unfold_mutable_list(struct s_node * x) =
  ((x != NULL && x->next != NULL)
  ==> (\mutable(x) == \mutable(x->next) &&
       \writable(x) == \writable(x->next)) ) )

// ---------------------------------------------------------------------------------------------------------
/*
_(logic \bool maintainsAcross(struct s_node * x, struct s_node * y, \state enter, \state exit) = 
	((! (x \in \at(enter, sllN(y)))) ==> \at(enter, sllN(y)) == \at(exit, sllN(y))) &&
	((! (x \in \at(enter, sllN(y)))) ==> \at(enter, sll(y)) == \at(exit, sll(y))) &&
	((! (x \in \at(enter, sllN(y)))) ==> \at(enter, sllKeys(y)) == \at(exit, sllKeys(y)))
	;)
	*/
/*
_(logic \bool disjointMaintainsAcross(struct s_node * x, struct s_node * y, \state enter, \state exit) =
	(\disjoint(\at(enter, N(x)), \at(enter, N(y))) ==> 
             \at(enter, N(x)) == \at(exit, N(x))) &&
	(\disjoint(\at(enter, N(x)), \at(enter, N(y))) ==> 
             \at(enter, sll(x)) == \at(exit, sll(x))) &&
	(\disjoint(\at(enter, N(x)), \at(enter, N(y))) ==> 
             \at(enter, keys(x)) == \at(exit, keys(x))) 
	;)
*/

/*
_(logic \bool maintainsAcrossLseg(struct s_node * x, struct s_node * y, \state enter, \state exit) = 
	((! (x \in \at(enter, lsegN(y, x)))) ==> \at(enter, lsegN(y, x)) == \at(exit, lsegN(y, x))) &&
	((! (x \in \at(enter, lsegN(y, x)))) ==> \at(enter, lseg (y, x)) == \at(exit, lseg (y, x))) &&
	((! (x \in \at(enter, lsegN(y, x)))) ==> \at(enter, lsegk(y, x)) == \at(exit, lsegk(y, x))) 
	;)
*/


#endif
