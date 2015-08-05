#include <vcc.h>

void update(int *p)
  _(requires \true)
	_(writes p)
  _(ensures *p == 21)
{
	*p = 21;
}

int main() {
	int a,b;
	a = 3;
  b = 7;
	
	_(assert b == 7)
	update(&b);
  _(assert b == 21)
}
