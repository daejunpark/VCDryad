
Node * sll_reverse(Node * x)
	_(requires sll(x))
	_(ensures  sll(\result))
	_(ensures  keys(\result) == \old(keys(x)))
{
	_(assume x != NULL ==> \writable(x) && \mutable(x))
	_(ghost \objset G0 = N(x) ;)	

	Node * y = NULL;

	while (x != NULL) 
		_(invariant x != NULL ==> \writable(x) && \mutable(x))
		_(invariant sll(x))
		_(invariant sll(y))
		_(invariant \disjoint(N(x), N(y)))
		_(invariant \intset_union(keys(x), keys(y)) == \old(keys(x)))
	{
		_(ghost \state S0 = \now() ;)

		Node * tmp = x->next;
		_(assume unfoldAll(x))
		_(ghost \state S1 = \now() ;)
		_(assert \disjoint(N(tmp), N(y)))

		x->next = y;
		_(assume unfoldAll(x))
		_(ghost \state S2 = \now() ;)
		_(assume maintainsAcross(x, y, S1, S2))
		_(assume maintainsAcross(x, tmp, S1, S2))

		y = x;
		_(ghost \state S3 = \now() ;)
   
		x = tmp;
		_(ghost \state S4 = \now() ;)

		_(assume x != NULL ==> \writable(x) && \mutable(x))
	}
	return y;
}

