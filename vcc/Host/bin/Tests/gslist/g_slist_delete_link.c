#include "dryad_gslist_sll.h"


Node * g_slist_remove_link(Node * list, Node * link)
	_(requires sll(list))
	_(requires sll(link) && \malloc_root(link)) 
	_(ensures sll(\result)) 
	_(ensures sll(link) && \malloc_root(link)) 
	_(ensures !\oset_in(link, \old(sll_reach(list))) ==> \old(sll_reach(list)) == sll_reach(\result)) 
	_(ensures  \oset_in(link, \old(sll_reach(list))) ==> (sll_reach(\result) == \oset_diff(\old(sll_reach(list)), \oset_singleton(link)))) 
;

_(dryad)
Node * g_slist_delete_link(Node * list, Node * link_)
	_(requires sll(list))
	_(requires sll(link_) && \malloc_root(link_))
	_(ensures sll(\result))
	_(ensures !\oset_in(link_, \old(sll_reach(list))) ==> \old(sll_reach(list)) == sll_reach(\result)) 
	_(ensures  \oset_in(link_, \old(sll_reach(list))) ==> (sll_reach(\result) == \oset_diff(\old(sll_reach(list)), \oset_singleton(link_))))
{
	_(assume \mutable(link_) && \writable(link_))
	list = g_slist_remove_link(list, link_);
	free(link_); 
	return list;
}

