#include "sll.h"
Node * g_slist_remove_link(Node * list, Node * link)
	_(requires _dryad_sll(list))
	_(requires _dryad_sll(link) && \malloc_root(link)) 
	_(ensures _dryad_sll(\result)) 
	_(ensures _dryad_sll(link) && \malloc_root(link)) 
	_(ensures !(link \in \old(_dryad_N(list))) ==> \old(_dryad_N(list)) == _dryad_N(\result)) 
	_(ensures   link \in \old(_dryad_N(list)) ==> (_dryad_N(\result) == (\old(_dryad_N(list)) \diff {link}))) 
;

Node * g_slist_delete_link(Node * list, Node * link_)
	_(requires _dryad_sll(list))
	_(requires _dryad_sll(link_) && \malloc_root(link_))
	_(ensures _dryad_sll(\result))
	_(ensures !(link_ \in \old(_dryad_N(list))) ==> \old(_dryad_N(list)) == _dryad_N(\result)) 
	_(ensures   link_ \in \old(_dryad_N(list)) ==> (_dryad_N(\result) == (\old(_dryad_N(list)) \diff {link_})))
{
	_(assert \malloc_root(link_))
	_(assume \mutable(link_) && \writable(link_))
	list = g_slist_remove_link(list, link_);
	free(link_); 
	return list;
}

