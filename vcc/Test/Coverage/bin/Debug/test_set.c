#include <vcc.h>

void foo() {
	int a, b, c;

	_(assert ({&a, &b, &c} \diff {&a, &b}) == {&c})
}
