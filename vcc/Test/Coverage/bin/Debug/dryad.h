#ifndef DRYAD_LIST_DEFS_H
#define DRYAD_LIST_DEFS_H

#include <stdlib.h>
#include "intset_defs.h"
#include "intbag_defs.h"

// N is an uninterpreted function, representing the reach set.
// N(NULL) is empty, and root \in N(root) if root is not NULL.
_(abstract \objset _dryad_N(struct node *root)
	_(reads \universe())
	_(ensures ((root != NULL) ==> (root \in \result))
			&& ((root == NULL) ==> (\result == {})))
	;)

// sll is an uninterpreted function, representing the singly-linked list.
// sll(NULL) is true.
_(abstract \bool _dryad_sll(struct node * hd)
	_(reads \universe())
	_(ensures (hd == NULL) ==> \result)
	;)

_(abstract \bool _dryad_srtl(struct node * hd)
	_(reads \universe())
	_(ensures hd == NULL ==> \result)
	;)
		//_(ensures hd != NULL ==> sll(hd) && \intset_lt(hd->key, keys(hd->next)))
_(abstract \bool _dryad_rsrtl(struct node * hd)
	_(reads \universe())
	_(ensures hd == NULL ==> \result)
	;)


_(abstract \intset _dryad_keys(struct node * hd)
	_(reads \universe())
	_(ensures (hd != NULL ==> \intset_in(hd->key, \result)))
	_(ensures (hd == NULL ==> (\result == \intset_empty)))
	;)

_(abstract \intbag _dryad_keyb(struct node * hd)
	_(reads \universe())
	_(ensures (hd != NULL ==> \intbag_in(hd->key, \result)))
	_(ensures (hd == NULL ==> (\result == \intbag_empty)))
	;)

_(abstract \natural _dryad_llen(struct node * hd)
	_(reads \universe())
	_(ensures hd != NULL ==> \result > 0)
	_(ensures hd == NULL ==> \result == 0)
	;)

// ----------------------------------------------------------------------------
// list segment definitions
// ----------------------------------------------------------------------------
_(abstract \objset _dryad_lsegN(struct node * hd, struct node * tl)
	_(reads \universe())
	_(ensures hd == NULL ==> \result == {})
	_(ensures hd == tl ==> \result == {})
	_(ensures hd != tl ==> hd \in \result)
	_(ensures tl == NULL ==> (\result == _dryad_N(hd)))
  ;)

_(abstract \intset _dryad_lsegk(struct node * hd, struct node * tl)
	_(reads \universe())
	_(ensures (hd != tl ==> \intset_in(hd->key, \result)))
	_(ensures (hd == NULL ==> (\result == \intset_empty)))
	_(ensures (hd == tl ==> (\result == \intset_empty)))
	_(ensures tl == NULL ==> (\result == _dryad_keys(hd)))
  ;)

_(abstract \intbag _dryad_lsegb(struct node * hd, struct node * tl)
	_(reads \universe())
	_(ensures (hd != tl ==> \intbag_in(hd->key, \result)))
	_(ensures (hd == NULL ==> (\result == \intbag_empty)))
	_(ensures (hd == tl ==> (\result == \intbag_empty)))
	_(ensures (tl == NULL ==> (\result == _dryad_keyb(hd))))
	;)

_(abstract \natural _dryad_lseglen(struct node * hd, struct node * tl)
	_(reads \universe())
	_(ensures hd == tl ==> \result == 0)
	_(ensures hd == NULL ==> \result == 0)
	_(ensures hd != tl ==> \result > 0)
	_(ensures tl == NULL ==> \result == _dryad_llen(hd))
	;)

_(abstract \bool _dryad_lseg(struct node * hd, struct node * tl)
  _(reads \universe())
  _(ensures hd == NULL ==> \result)
  _(ensures hd == tl ==> \result)
  _(ensures tl == NULL ==> (\result == _dryad_sll(hd)))
  _(ensures (_dryad_sll(tl) && \disjoint(_dryad_N(tl), _dryad_lsegN(hd, tl))) ==>
                          (_dryad_sll(hd) 
						  && _dryad_keys(hd) == \intset_union(_dryad_keys(tl), _dryad_lsegk(hd, tl))
						  && _dryad_keyb(hd) == \intbag_union(_dryad_keyb(tl), _dryad_lsegb(hd, tl))
						  ) )
  _(ensures (tl != NULL && _dryad_sll(tl->next) 
             && \disjoint(_dryad_N(tl->next), _dryad_lsegN(hd, tl)) 
		     && (! (tl \in _dryad_N(tl->next)) ) 
		     && (! (tl \in _dryad_lsegN(hd, tl)))   ) ==>
                   (  _dryad_lseg (hd, tl->next) 
				   && _dryad_lsegk(hd, tl->next) == \intset_union(\intset_singleton(tl->key), _dryad_lsegk(hd, tl)) 
				   && _dryad_lsegb(hd, tl->next) == \intbag_union(\intbag_singleton(tl->key), _dryad_lsegb(hd, tl))
				   && _dryad_lsegN(hd, tl->next) == ({tl} \union _dryad_lsegN(hd, tl))   ) )
  ;)

_(abstract \bool _dryad_srtlseg(struct node * hd, struct node * tl)
	_(reads \universe())
	_(ensures hd == NULL ==> \result)
	_(ensures hd == tl ==> \result)
	_(ensures tl == NULL ==> (\result == _dryad_srtl(hd)))
	_(ensures (_dryad_srtl(tl) && \disjoint(_dryad_N(tl), _dryad_lsegN(hd, tl))) ==>
				(_dryad_srtl(hd)
				&& _dryad_keys(hd) == \intset_union(_dryad_keys(tl), _dryad_lsegk(hd, tl))
				&& _dryad_keyb(hd) == \intbag_union(_dryad_keyb(tl), _dryad_lsegb(hd, tl)) ) )
	_(ensures (tl != NULL && _dryad_srtl(tl->next) 
				&& \disjoint(_dryad_N(tl->next), _dryad_lsegN(hd, tl))
				&& (! (tl \in _dryad_N(tl->next))) && (! (tl \in _dryad_lsegN(hd, tl)))) ==>
				(_dryad_srtlseg(hd, tl->next)
				&& _dryad_lsegk(hd, tl->next) == \intset_union(\intset_singleton(tl->key), _dryad_lsegk(hd, tl))
				&& _dryad_lsegb(hd, tl->next) == \intbag_union(\intbag_singleton(tl->key), _dryad_lsegb(hd, tl))
				&& _dryad_lsegN(hd, tl->next) == ({tl} \union _dryad_lsegN(hd, tl)) ) )
	;)

// ----------------------------------------------------------------------------------------------------------------------------

// unfold N w.r.t. the location root
_(pure \bool _dryad_unfoldN(struct node * hd)
	_(reads \universe())
	_(ensures \result == (hd != NULL ==>
		(_dryad_N(hd) == (_dryad_N(hd->next) \union {hd})) ) )
	;)

_(pure \bool _dryad_unfoldKeys(struct node * hd)
	_(reads \universe())
	_(ensures \result == 
		(hd != NULL ==> (_dryad_keys(hd) == (\intset_union(_dryad_keys(hd->next), \intset_singleton(hd->key))))) )
	;)

_(pure \bool _dryad_unfoldKeyb(struct node * hd)
	_(reads \universe())
	_(ensures \result == 
		(hd != NULL ==> (_dryad_keyb(hd) == (\intbag_union(_dryad_keyb(hd->next), \intbag_singleton(hd->key))))) )
	;)

_(pure \bool _dryad_unfoldLen(struct node * hd)
	_(reads \universe())
	_(ensures \result ==
		(hd != NULL ==> (_dryad_llen(hd) == _dryad_llen(hd->next) + 1)) )
	;)

// unfold sll w.r.t. the location hd
_(pure \bool _dryad_unfoldSll(struct node * hd)
	_(reads \universe())
	_(ensures \result == (hd != NULL ==>
		(_dryad_sll(hd) <==> 
			(_dryad_sll(hd->next) && 
			(! (hd \in _dryad_N(hd->next))) ) ) ) )
	;)
//TODO: && getKey(hd) <= getKey(hd->next) [probably remove]

_(pure \bool _dryad_unfoldSrtl(struct node * hd)
	_(reads \universe())
	_(ensures \result == (hd != NULL ==>
		(_dryad_srtl(hd) <==>
			(_dryad_srtl(hd->next) &&
			!(hd \in _dryad_N(hd->next)) &&
			\intset_le(hd->key, _dryad_keys(hd->next)) ) ) ) )
	;)

_(pure \bool _dryad_unfoldRSrtl(struct node * hd)
	_(reads \universe())
	_(ensures \result == (hd != NULL ==>
		(_dryad_rsrtl(hd) <==>
			(_dryad_rsrtl(hd->next) &&
			!(hd \in _dryad_N(hd->next)) &&
			\intset_ge(hd->key, _dryad_keys(hd->next)) ) ) ) )
	;)

/* TODO: [probably remove]
// unfold minKey w.r.t. the location root
_(pure \bool unfoldMinKey(struct node * hd)
	_(reads \universe())
	_(ensures \result == (hd != NULL ==>
		getKey(hd) == getMinKey(getKey(hd), getKey(hd->next)) ))
	;)
*/

// ----------------------------------------------------------------------------------------------------------------------------
// unfolding of the list segment functions/predicate
// ----------------------------------------------------------------------------------------------------------------------------
_(pure \bool _dryad_unfoldLsegN(struct node * hd, struct node * tl)
	_(reads \universe())
	_(ensures \result == (hd != tl ==> 
                       (_dryad_lsegN(hd, tl) == (_dryad_lsegN(hd->next, tl) \union {hd})) ) )
  ;)

_(pure \bool _dryad_unfoldLsegk(struct node * hd, struct node * tl)
	_(reads \universe())
	_(ensures \result == (hd != tl ==> 
					   (_dryad_lsegk(hd, tl) == (\intset_union(_dryad_lsegk(hd->next,tl), \intset_singleton(hd->key)))) ) )
	;)

_(pure \bool _dryad_unfoldLsegb(struct node * hd, struct node * tl)
	_(reads \universe())
	_(ensures \result == (hd != tl ==>
					(_dryad_lsegb(hd, tl) == (\intbag_union(_dryad_lsegb(hd->next, tl), \intbag_singleton(hd->key)))) ) )
	;)

_(pure \bool _dryad_unfoldLseglen(struct node * hd, struct node * tl)
	_(reads \universe())
	_(ensures \result == (hd != tl ==>
			(_dryad_lseglen(hd, tl) == (_dryad_lseglen(hd->next, tl) + 1)) ) )
	;)

_(pure \bool _dryad_unfoldLseg(struct node * hd, struct node * tl)
  _(reads \universe())
  _(ensures \result == (hd != tl ==>
       (_dryad_lseg(hd,tl) <==> (_dryad_lseg(hd->next,tl) 
					  && (! (hd \in _dryad_lsegN(hd->next,tl))) ) ) ) )
  ;)
  			//&& getKey(hd) <= getKey(hd->next)

_(pure \bool _dryad_unfoldSrtlseg(struct node * hd, struct node * tl)
	_(reads \universe())
	_(ensures \result == (hd != tl ==>
		(_dryad_srtlseg(hd, tl) <==> (_dryad_srtlseg(hd->next, tl) 
							  && (! (hd \in _dryad_lsegN(hd->next, tl))) 
							  && \intset_le(hd->key, _dryad_lsegk(hd->next, tl)) ) ) ) )
		;)

// ----------------------------------------------------------------------------------------------------------------------------

// axioms needed to complete the proof
_(axiom \forall \objset os1, os2; \disjoint(os1, os2) <==> \subset(os1, (\universe() \diff os2)))
_(axiom \forall \objset os1, os2; \forall \object o; (os1 == (os2 \union {o})) ==> \subset(os2, os1)) // [sll-reverse]

_(abstract \bool _dryad_unfoldAll(\object o)
	_(reads \universe())
	_(ensures _dryad_unfoldN(o))
	_(ensures _dryad_unfoldSll(o))
	_(ensures _dryad_unfoldKeys(o))
	_(ensures _dryad_unfoldKeyb(o))
	_(ensures _dryad_unfoldLen(o))
	_(ensures _dryad_unfoldSrtl(o)) 
	_(ensures _dryad_unfoldRSrtl(o))
	;)
	// 	_(ensures unfoldMinKey(o))

_(abstract \bool _dryad_unfoldAllLseg(\object ohd, \object otl)
	_(reads \universe())
	_(ensures _dryad_unfoldLsegN(ohd, otl))
	_(ensures _dryad_unfoldLsegk(ohd, otl))
	_(ensures _dryad_unfoldLsegb(ohd, otl))
	_(ensures _dryad_unfoldLseglen(ohd, otl))
	_(ensures _dryad_unfoldLseg (ohd, otl))
	_(ensures _dryad_unfoldSrtlseg(ohd, otl))
	;)

_(abstract \bool _dryad_unfoldAllSrtlseg(\object ohd, \object otl)
	_(reads \universe())
	_(ensures _dryad_unfoldAllLseg(ohd, otl))
	_(ensures _dryad_unfoldSrtlseg(ohd, otl))
	;)

_(abstract \bool _dryad_unfoldAllSort(\object o)
	_(reads \universe())
	_(ensures _dryad_unfoldAll(o))
	_(ensures _dryad_unfoldSrtl(o)) ;)

_(abstract \bool _dryad_unfoldAllSortRev(\object o)
	_(reads \universe())
	_(ensures _dryad_unfoldAll(o))
	_(ensures _dryad_unfoldRSrtl(o)) ;)

_(logic \bool _dryad_maintainsAcross(struct node * x, struct node * y, \state enter, \state exit) = 
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_N(y)) == \at(exit, _dryad_N(y))) &&
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_sll(y)) == \at(exit, _dryad_sll(y))) &&
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_keys(y)) == \at(exit, _dryad_keys(y))) &&
	((! (x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_keyb(y)) == \at(exit, _dryad_keyb(y))) &&
	((!(x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_srtl(y)) == \at(exit, _dryad_srtl(y))) &&
	((!(x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_rsrtl(y)) == \at(exit, _dryad_rsrtl(y)))
	;)

// TODO: probably remove
// 	((! (x \in \at(enter, N(y)))) ==> \at(enter, getKey(y)) == \at(exit, getKey(y)))
// ((! (x \in \at(enter, N(y)))) ==> \at(enter, \malloc_root(y)) == \at(exit, \malloc_root(y))) && 

_(logic \bool maintainsAcrossSort(struct node * x, struct node * y, \state enter, \state exit) = 
	_dryad_maintainsAcross(x, y, enter, exit) &&
	((!(x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_srtl(y)) == \at(exit, _dryad_srtl(y)))
	;)
_(logic \bool maintainsAcrossSortRev(struct node * x, struct node * y, \state enter, \state exit) = 
	_dryad_maintainsAcross(x, y, enter, exit) &&
	((!(x \in \at(enter, _dryad_N(y)))) ==> \at(enter, _dryad_rsrtl(y)) == \at(exit, _dryad_rsrtl(y)))
	;)

_(logic \bool _dryad_maintainsAcrossLseg(struct node * x, struct node * b, struct node * e, \state enter, \state exit) = 
	((! (x \in \at(enter, _dryad_lsegN(b, e)))) ==> \at(enter, _dryad_lsegN(b, e)) == \at(exit, _dryad_lsegN(b, e))) &&
	((! (x \in \at(enter, _dryad_lsegN(b, e)))) ==> \at(enter, _dryad_lseg (b, e)) == \at(exit, _dryad_lseg (b, e))) &&
	((! (x \in \at(enter, _dryad_lsegN(b, e)))) ==> \at(enter, _dryad_lsegk(b, e)) == \at(exit, _dryad_lsegk(b, e))) &&
	((! (x \in \at(enter, _dryad_lsegN(b, e)))) ==> \at(enter, _dryad_lsegb(b, e)) == \at(exit, _dryad_lsegb(b, e))) &&
	((! (x \in \at(enter, _dryad_lsegN(b, e)))) ==> \at(enter, _dryad_srtlseg(b, e)) == \at(exit, _dryad_srtlseg(b, e)))
	;)

_(logic \bool _dryad_maintainsAcrossSrtlseg(struct node * x, struct node * b, struct node *e, \state enter, \state exit) =
	_dryad_maintainsAcrossLseg(x, b, e, enter, exit) &&
	((! (x \in \at(enter, _dryad_lsegN(b, e)))) ==> \at(enter, _dryad_srtlseg(b, e)) == \at(exit, _dryad_srtlseg(b, e)))
	;)

_(logic \bool _dryad_disjointMaintainsAcross(struct node * x, struct node * y, \state enter, \state exit) =
	(\disjoint(\at(enter, _dryad_N(x)), \at(enter, _dryad_N(y))) ==> 
             \at(enter, _dryad_N(x)) == \at(exit, _dryad_N(x))) &&
	(\disjoint(\at(enter, _dryad_N(x)), \at(enter, _dryad_N(y))) ==> 
             \at(enter, _dryad_sll(x)) == \at(exit, _dryad_sll(x))) &&
	(\disjoint(\at(enter, _dryad_N(x)), \at(enter, _dryad_N(y))) ==> 
             \at(enter, _dryad_keys(x)) == \at(exit, _dryad_keys(x))) 
	;)

/* TODO: probably remove
	(\disjoint(\at(enter, N(x)), \at(enter, N(y))) ==> 
             \at(enter, getKey(x)) == \at(exit, getKey(x))) 
*/

/*
_(logic \bool maintainsAcrossLseg(struct node * x, struct node * y, \state enter, \state exit) = 
	((! (x \in \at(enter, lsegN(y, x)))) ==> \at(enter, lsegN(y, x)) == \at(exit, lsegN(y, x))) &&
	((! (x \in \at(enter, lsegN(y, x)))) ==> \at(enter, lseg (y, x)) == \at(exit, lseg (y, x))) &&
	((! (x \in \at(enter, lsegN(y, x)))) ==> \at(enter, lsegk(y, x)) == \at(exit, lsegk(y, x))) 
	;)
*/


#endif
