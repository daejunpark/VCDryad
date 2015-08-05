#include <vcc.h>
#include <stdlib.h>

typedef struct node {
	int key;
	struct node * next;
} Node;

Node * node_init(int k)
{
	// leaf is a location
	Node * leaf = (Node *) malloc(sizeof(Node));
	_(assume leaf != NULL)
	// key is field [to be represented as mapping from locations to ints]
	leaf->key = k;
	// next is a field [to be represented as mapping from locations to locations]
	leaf->next = NULL;
	return leaf;
}

int test_result(int m) 
	_(ensures m == 0 ==> \result == 1)
{
	if (m == 0) { return 1;}
 	else {return -1;}
}

_(pure
\objset test_ghost()
{
	\objset a, b;
	a = {};
	b = {(void *)40};
	//a = \universe() \diff b;
	_(assert (void *) 40 \in b)
	_(ghost \state s0 = \now();)
})


void test()
{
	Node * n = (Node *) malloc(sizeof(Node));
	_(assume n != NULL)
	Node * m = (Node *) malloc(sizeof(Node));
	_(assume m != NULL)
	int a = 7;
	n->next = m;
	n->key = a;
	m->next = NULL;
	m->key = 0;
}
