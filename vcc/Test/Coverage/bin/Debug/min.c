#include <vcc.h>

int min(int x, int y) 
  _(requires \true)
  _(ensures \result <= x && \result <= y)
{
	if (x < y) 
		return x;
	return y;
}

int main()
{
  int x, y, z;
  z = min(x,y);
  _(assert z <= x);
  return 0;
}
