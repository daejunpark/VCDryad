#include "dryad_avl.h"

_(logic \bool mutable_avl(AVLNode * x) = x != NULL ==> \mutable(x) && \writable(x))


_(pure) int get_height(AVLNode * x)
	_(reads \universe())
	_(returns x == NULL ? -1 : x->height)
{
	_(assume \thread_local(x))
	return x == NULL ? -1 : x->height;
}


_(dryad)
AVLNode * avl_balance(AVLNode * x)
	_(requires x != NULL)
	_(requires !\oset_in(x, avl_reach(x->left)))
	_(requires !(\intset_in(x->key, avl_keys(x->left))))
	_(requires avl(x->left))
	_(requires \intset_lt_one2(avl_keys(x->left), x->key))
	_(requires !\oset_in(x, avl_reach(x->right)))
	_(requires !(\intset_in(x->key, avl_keys(x->right))))
	_(requires avl(x->right))
	_(requires \intset_lt_one1(x->key, avl_keys(x->right)))
	_(requires \oset_disjoint(avl_reach(x->left), avl_reach(x->right)))
	_(requires avl_height(x->right) <= avl_height(x->left)  + 2)
	_(requires avl_height(x->left)  <= avl_height(x->right) + 2)

	_(ensures avl(\result))
	_(ensures avl_keys(\result) == \intset_union_one1(x->key, 
	            									\intset_union(\old(avl_keys(x->left)), \old(avl_keys(x->right)))))
	_(ensures ((\old(avl_height(x->left)) == \old(avl_height(x->right))) 
				&& (avl_height(\result) == \old(avl_height(x->left)) + 1))

		   || ((\old(avl_height(x->left)) == (\old(avl_height(x->right)) + 1))
				&& (avl_height(\result) ==  \old(avl_height(x->left)) + 1))

	       || ((\old(avl_height(x->right)) == (\old(avl_height(x->left)) + 1)) 
				&& (avl_height(\result) ==  \old(avl_height(x->right)) + 1)) 

		   || (x->left != NULL && 
				((\old(avl_height(x->left)) == (\old(avl_height(x->right)) + 2))
				 && (\old(avl_height(x->left->left)) == \old(avl_height(x->left->right)))
				 && (avl_height(\result) == \old(avl_height(x->left)) + 1))
			 || ((\old(avl_height(x->left)) == (\old(avl_height(x->right)) + 2))
				 && (\old(avl_height(x->left->left)) != \old(avl_height(x->left->right)))
				 && (avl_height(\result) == \old(avl_height(x->left)))) )
		   || (x->right != NULL && 
				((\old(avl_height(x->right)) == (\old(avl_height(x->left)) + 2))
				 && (\old(avl_height(x->right->left)) == \old(avl_height(x->right->right)))
				 && (avl_height(\result) == \old(avl_height(x->right)) + 1))
			 || ((\old(avl_height(x->right)) == (\old(avl_height(x->left)) + 2))
				 && (\old(avl_height(x->right->left)) != \old(avl_height(x->right->right)))
				 && (avl_height(\result) == \old(avl_height(x->right)))) )  )
{
	_(assume mutable_avl(x))
	_(assume mutable_avl(x->left))
	_(assume mutable_avl(x->right))

	int lht = get_height(x->left);
	_(assume lht < INT_MAX - 1)
	int rht = get_height(x->right);
	_(assume rht < INT_MAX - 1)

	AVLNode * right = x->right;
	AVLNode * left  = x->left;

	if (rht == lht + 2) {

		int rlht = get_height(right->left);
		_(assume rlht < INT_MAX - 1)

		int rrht = get_height(right->right);
		_(assume rrht < INT_MAX - 1)

		AVLNode * right_left = right->left;
		AVLNode * right_right = right->right;


		if (rlht <= rrht) {
      int inc_rlht = rlht + 1;
			x->height = inc_rlht;

			x->right = right_left;
			
      int inc_inc_rlht = rlht + 2;
			right->height = inc_inc_rlht;

			right->left = x;

			return right;

		} else {
			_(assume mutable_avl(right_left))
			AVLNode * right_left_left = right_left->left;

			AVLNode * right_left_right = right_left->right;

      int inc_lht = lht + 1;
			x->height = inc_lht;

			x->right = right_left_left;
			
      int inc_rrht = rrht + 1;
			right->height = inc_rrht;

			right->left = right_left_right;
			
      int inc_inc_lht = lht + 2;
			right_left->height = inc_inc_lht;

			right_left->left = x;

			right_left->right = right;

			return right_left;

		}
	} else if (lht == rht + 2) {
    //_(assume unfold_avl_all(x->right))

		int llht = get_height(left->left);
		_(assume llht < INT_MAX - 1)
		int lrht = get_height(left->right);
		_(assume lrht < INT_MAX - 1)

		AVLNode * left_left = left->left;
		AVLNode * left_right = left->right;

		if (lrht <= llht) {
      int inc_lrht = lrht + 1;
			x->height = inc_lrht;

			x->left = left_right;

      int inc_inc_lrht = lrht + 2;
			left->height = inc_inc_lrht;

			left->right = x;

			return left;
		} else { // lrht > llht
			// rotate-left |> rotate-right
			_(assume mutable_avl(left_right))
			AVLNode * left_right_left = left_right->left;

			AVLNode * left_right_right = left_right->right;

      int inc_rht = rht + 1;
			x->height = inc_rht;

			x->left   = left_right_right;

      int inc_llht = llht + 1;
			left->height = inc_llht;

			left->right = left_right_left;

      int inc_inc_rht = rht + 2;
			left_right->height = inc_inc_rht;

			left_right->left = left;

			left_right->right = x;

			return left_right;
		}
	} else if (rht == lht + 1) {
  
    int inc_rht = rht + 1;
		x->height = inc_rht;

		return x;
	} else {
		
    int inc_lht = lht + 1;
		x->height = inc_lht;

		return x;
	
	}
}
