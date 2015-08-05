#include <vcc.h>

_(axiom \forall \objset os1, os2; 
	\disjoint(os1, os2) <==> \subset(os1, (\universe() \diff os2))
)
	
