#include <vcc.h>

int min(int x, int y) 
	_(requires x > 0 && y > 0)
	_(ensures x <  y ==> \result == x)
	_(ensures x >= y ==> \result == y)
	_(ensures \result == x || \result == y)
{
	int r;
	if (x < y) {
		r = x;
	} else {
		r = y;
	}
	return r;
}
