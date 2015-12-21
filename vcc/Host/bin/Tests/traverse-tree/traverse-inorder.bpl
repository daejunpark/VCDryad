axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

const unique ^$##thread_id: $ctype;

axiom $def_math_type(^$##thread_id);

type $##thread_id;

const unique ^$##club: $ctype;

axiom $def_math_type(^$##club);

type $##club;

const unique ^t_node: $ctype;

axiom $is_span_sequential(^t_node);

axiom $def_struct_type(^t_node, 24, false, false);

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2(#s1, #s2, #p, ^t_node) } $inv2(#s1, #s2, #p, ^t_node) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2_without_lemmas(#s1, #s2, #p, ^t_node) } $inv2_without_lemmas(#s1, #s2, #p, ^t_node) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall p: $ptr, q: $ptr, s: $state :: { $in(q, $composite_extent(s, p, ^t_node)) } $in(q, $composite_extent(s, p, ^t_node)) == (q == p));

const unique t_node.left: $field;

axiom $def_phys_field(^t_node, t_node.left, $ptr_to(^t_node), false, 0);

const unique t_node.right: $field;

axiom $def_phys_field(^t_node, t_node.right, $ptr_to(^t_node), false, 8);

const unique t_node.key: $field;

axiom $def_phys_field(^t_node, t_node.key, ^^i4, false, 16);

const unique ^$#_purecall_handler#1: $ctype;

axiom $def_fnptr_type(^$#_purecall_handler#1);

type $#_purecall_handler#1;

const unique ^$#_invalid_parameter_handler#2: $ctype;

axiom $def_fnptr_type(^$#_invalid_parameter_handler#2);

type $#_invalid_parameter_handler#2;

const unique ^$#traverse_inorder.c..36261#3: $ctype;

axiom $def_fnptr_type(^$#traverse_inorder.c..36261#3);

type $#traverse_inorder.c..36261#3;

const unique ^$#_PtFuncCompare#4: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#4);

type $#_PtFuncCompare#4;

const unique ^$#_PtFuncCompare#5: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#5);

type $#_PtFuncCompare#5;

const unique ^$#_PtFuncCompare#6: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#6);

type $#_PtFuncCompare#6;

const unique ^$#_PtFuncCompare#7: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#7);

type $#_PtFuncCompare#7;

const unique ^$#_onexit_t#8: $ctype;

axiom $def_fnptr_type(^$#_onexit_t#8);

type $#_onexit_t#8;

function F#tree(#s: $state, SP#root: $ptr) : bool;

const unique cf#tree: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#tree(#s, SP#root) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> F#tree(#s, SP#root));

axiom $function_arg_type(cf#tree, 0, ^^bool);

axiom $function_arg_type(cf#tree, 1, $ptr_to(^t_node));

procedure tree(SP#root: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> $result;
  free ensures $result == F#tree($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#intree(#s: $state, SP#root: $ptr) : bool;

const unique cf#intree: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#intree(#s, SP#root) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> F#intree(#s, SP#root));

axiom $function_arg_type(cf#intree, 0, ^^bool);

axiom $function_arg_type(cf#intree, 1, $ptr_to(^t_node));

procedure intree(SP#root: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> $result;
  free ensures $result == F#intree($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#tree_reach(#s: $state, SP#root: $ptr) : $oset;

const unique cf#tree_reach: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#tree_reach(#s, SP#root) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#root, ^t_node)) ==> $oset_in($phys_ptr_cast(SP#root, ^t_node), F#tree_reach(#s, SP#root))) && ($is_null($phys_ptr_cast(SP#root, ^t_node)) ==> F#tree_reach(#s, SP#root) == $oset_empty()));

axiom $function_arg_type(cf#tree_reach, 0, ^$#oset);

axiom $function_arg_type(cf#tree_reach, 1, $ptr_to(^t_node));

procedure tree_reach(SP#root: $ptr) returns ($result: $oset);
  ensures $non_null($phys_ptr_cast(SP#root, ^t_node)) ==> $oset_in($phys_ptr_cast(SP#root, ^t_node), $result);
  ensures $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> $result == $oset_empty();
  free ensures $result == F#tree_reach($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#intree_reach(#s: $state, SP#root: $ptr) : $oset;

const unique cf#intree_reach: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#intree_reach(#s, SP#root) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#root, ^t_node)) ==> $oset_in($phys_ptr_cast(SP#root, ^t_node), F#intree_reach(#s, SP#root))) && ($is_null($phys_ptr_cast(SP#root, ^t_node)) ==> F#intree_reach(#s, SP#root) == $oset_empty()));

axiom $function_arg_type(cf#intree_reach, 0, ^$#oset);

axiom $function_arg_type(cf#intree_reach, 1, $ptr_to(^t_node));

procedure intree_reach(SP#root: $ptr) returns ($result: $oset);
  ensures $non_null($phys_ptr_cast(SP#root, ^t_node)) ==> $oset_in($phys_ptr_cast(SP#root, ^t_node), $result);
  ensures $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> $result == $oset_empty();
  free ensures $result == F#intree_reach($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#tree_size(#s: $state, SP#root: $ptr) : int;

const unique cf#tree_size: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#tree_size(#s, SP#root) } 1 < $decreases_level ==> ($is_null($phys_ptr_cast(SP#root, ^t_node)) ==> F#tree_size(#s, SP#root) == 0) && ($non_null($phys_ptr_cast(SP#root, ^t_node)) ==> F#tree_size(#s, SP#root) > 0));

axiom $function_arg_type(cf#tree_size, 0, ^^mathint);

axiom $function_arg_type(cf#tree_size, 1, $ptr_to(^t_node));

procedure tree_size(SP#root: $ptr) returns ($result: int);
  ensures $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> $result == 0;
  ensures $non_null($phys_ptr_cast(SP#root, ^t_node)) ==> $result > 0;
  free ensures $result == F#tree_size($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#tree_lsize(#s: $state, SP#root: $ptr) : int;

const unique cf#tree_lsize: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#tree_lsize(#s, SP#root) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> F#tree_lsize(#s, SP#root) == 0);

axiom $function_arg_type(cf#tree_lsize, 0, ^^mathint);

axiom $function_arg_type(cf#tree_lsize, 1, $ptr_to(^t_node));

procedure tree_lsize(SP#root: $ptr) returns ($result: int);
  ensures $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> $result == 0;
  free ensures $result == F#tree_lsize($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#tree_rsize(#s: $state, SP#root: $ptr) : int;

const unique cf#tree_rsize: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#tree_rsize(#s, SP#root) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> F#tree_rsize(#s, SP#root) == 0);

axiom $function_arg_type(cf#tree_rsize, 0, ^^mathint);

axiom $function_arg_type(cf#tree_rsize, 1, $ptr_to(^t_node));

procedure tree_rsize(SP#root: $ptr) returns ($result: int);
  ensures $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> $result == 0;
  free ensures $result == F#tree_rsize($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#tree_order(#s: $state, SP#root: $ptr) : int;

const unique cf#tree_order: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#tree_order(#s, SP#root) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> F#tree_order(#s, SP#root) == 0);

axiom $function_arg_type(cf#tree_order, 0, ^^mathint);

axiom $function_arg_type(cf#tree_order, 1, $ptr_to(^t_node));

procedure tree_order(SP#root: $ptr) returns ($result: int);
  ensures $is_null($phys_ptr_cast(SP#root, ^t_node)) ==> $result == 0;
  free ensures $result == F#tree_order($s, SP#root);
  free ensures $call_transition(old($s), $s);



procedure inorder(P#x: $ptr, P#n: int) returns ($result: int);
  requires F#tree($s, $phys_ptr_cast(P#x, ^t_node));
  modifies $s, $cev_pc;
  free ensures $in_range_i4($result);
  ensures F#intree($s, $phys_ptr_cast(P#x, ^t_node));
  ensures F#tree_reach($s, $phys_ptr_cast(P#x, ^t_node)) == F#intree_reach($s, $phys_ptr_cast(P#x, ^t_node));
// INV:BEGIN
  ensures F#tree($s, $phys_ptr_cast(P#x, ^t_node));
  ensures F#tree_reach($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_reach(old($s), $phys_ptr_cast(P#x, ^t_node));
// INV:END
  ensures $result == P#n + F#tree_size($s, $phys_ptr_cast(P#x, ^t_node));
  ensures F#tree_size($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size(old($s), $phys_ptr_cast(P#x, ^t_node));
  ensures $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_order($s, $phys_ptr_cast(P#x, ^t_node)) == P#n + F#tree_lsize($s, $phys_ptr_cast(P#x, ^t_node));
  ensures $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_size($s, $phys_ptr_cast(P#x, ^t_node)) == 1 + F#tree_lsize($s, $phys_ptr_cast(P#x, ^t_node)) + F#tree_rsize($s, $phys_ptr_cast(P#x, ^t_node));
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);

// INV:PTR: P#x
// INV:INT: P#n, $result
// INV:LST: tree



implementation inorder(P#x: $ptr, P#n: int) returns ($result: int)
{
  var stmtexpr5#6: $state;
  var SL#_dryad_S5: $state;
  var stmtexpr4#5: $state;
  var SL#_dryad_S4: $state;
  var stmtexpr3#4: $state;
  var SL#_dryad_S3: $state;
  var stmtexpr2#3: $state;
  var SL#_dryad_S2: $state;
  var stmtexpr1#2: $state;
  var SL#_dryad_S1: $state;
  var stmtexpr0#1: $state;
  var SL#_dryad_S0: $state;
  var L#n1: int where $in_range_i4(L#n1);
  var L#n2: int where $in_range_i4(L#n2);
  var L#n3: int where $in_range_i4(L#n3);
  var stmtexpr1#8: $oset;
  var stmtexpr0#7: $oset;
  var SL#_dryad_G1: $oset;
  var SL#_dryad_G0: $oset;
  var #wrTime$2^5.3: int;
  var #stackframe: int;

  anon3:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$2^5.3, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$2^5.3 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$2^5.3, (lambda #p: $ptr :: false));
    // assume true
    // assume @in_range_i4(n); 
    assume $in_range_i4(P#n);
    // assume @decreases_level_is(2147483647); 
    assume 2147483647 == $decreases_level;
    //  --- Dryad annotated function --- 
    // _math \oset _dryad_G0; 
    // _math \oset _dryad_G1; 
    // _dryad_G0 := tree_reach(x); 
    call SL#_dryad_G0 := tree_reach($phys_ptr_cast(P#x, ^t_node));
    assume $full_stop_ext(#tok$3^0.0, $s);
    // _math \oset stmtexpr0#7; 
    // stmtexpr0#7 := _dryad_G0; 
    stmtexpr0#7 := SL#_dryad_G0;
    // _dryad_G1 := _dryad_G0; 
    SL#_dryad_G1 := SL#_dryad_G0;
    // _math \oset stmtexpr1#8; 
    // stmtexpr1#8 := _dryad_G1; 
    stmtexpr1#8 := SL#_dryad_G1;
    // assume ==>(@_vcc_ptr_neq_null(x), ==(intree(x), &&(&&(&&(&&(&&(intree(*((x->left))), intree(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(intree_reach(*((x->left))), intree_reach(*((x->right))))))), @_vcc_oset_disjoint(intree_reach(*((x->left))), intree_reach(*((x->right))))), ==>(@_vcc_ptr_neq_null(*((x->left))), ==(+(+(tree_order(*((x->left))), tree_rsize(*((x->left)))), 1), *((x->key))))), ==>(@_vcc_ptr_neq_null(*((x->right))), ==(tree_order(*((x->right))), +(+(*((x->key)), tree_lsize(*((x->right)))), 1)))))); 
    assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#intree($s, $phys_ptr_cast(P#x, ^t_node)) == (F#intree($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && F#intree($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && !$oset_in($phys_ptr_cast(P#x, ^t_node), $oset_union(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)))) && $oset_disjoint(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) && ($non_null($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) ==> F#tree_order($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + F#tree_rsize($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1 == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node))) && ($non_null($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) ==> F#tree_order($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node)) + F#tree_lsize($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(intree_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(intree_reach(*((x->left))), intree_reach(*((x->right))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#intree_reach($s, $phys_ptr_cast(P#x, ^t_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^t_node)), $oset_union(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(tree(x), &&(&&(&&(tree(*((x->left))), tree(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(tree_reach(*((x->left))), tree_reach(*((x->right))))))), @_vcc_oset_disjoint(tree_reach(*((x->left))), tree_reach(*((x->right))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree($s, $phys_ptr_cast(P#x, ^t_node)) == (F#tree($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && F#tree($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && !$oset_in($phys_ptr_cast(P#x, ^t_node), $oset_union(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)))) && $oset_disjoint(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(tree_reach(*((x->left))), tree_reach(*((x->right))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_reach($s, $phys_ptr_cast(P#x, ^t_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^t_node)), $oset_union(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
    // assume ==(tree_lsize(x), tree_size(*((x->left)))); 
    assume F#tree_lsize($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_order(x), *((x->key)))); 
    assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_order($s, $phys_ptr_cast(P#x, ^t_node)) == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node));
    // assume ==(tree_rsize(x), tree_size(*((x->right)))); 
    assume F#tree_rsize($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_size(x), +(+(tree_size(*((x->left))), tree_size(*((x->right)))), 1))); 
    assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_size($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + F#tree_size($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1;
    // assume ==>(@_vcc_ptr_neq_null(x), &&(@_vcc_mutable(@state, x), @writes_check(x))); 
    assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> $mutable($s, $phys_ptr_cast(P#x, ^t_node)) && $top_writable($s, #wrTime$2^5.3, $phys_ptr_cast(P#x, ^t_node));
    // assume <(n, 2147483647); 
    assume P#n < 2147483647;
    assume true;
    // if (@_vcc_ptr_eq_null(x)) ...
    if ($is_null($phys_ptr_cast(P#x, ^t_node)))
    {
      anon1:
        // return n; 
        $result := P#n;
        assume true;
        assert $position_marker();
        goto #exit;
    }
    else
    {
      anon2:
        // assume ==>(@_vcc_ptr_neq_null(x), ==(intree(x), &&(&&(&&(&&(&&(intree(*((x->left))), intree(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(intree_reach(*((x->left))), intree_reach(*((x->right))))))), @_vcc_oset_disjoint(intree_reach(*((x->left))), intree_reach(*((x->right))))), ==>(@_vcc_ptr_neq_null(*((x->left))), ==(+(+(tree_order(*((x->left))), tree_rsize(*((x->left)))), 1), *((x->key))))), ==>(@_vcc_ptr_neq_null(*((x->right))), ==(tree_order(*((x->right))), +(+(*((x->key)), tree_lsize(*((x->right)))), 1)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#intree($s, $phys_ptr_cast(P#x, ^t_node)) == (F#intree($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && F#intree($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && !$oset_in($phys_ptr_cast(P#x, ^t_node), $oset_union(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)))) && $oset_disjoint(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) && ($non_null($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) ==> F#tree_order($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + F#tree_rsize($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1 == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node))) && ($non_null($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) ==> F#tree_order($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node)) + F#tree_lsize($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(intree_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(intree_reach(*((x->left))), intree_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#intree_reach($s, $phys_ptr_cast(P#x, ^t_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^t_node)), $oset_union(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree(x), &&(&&(&&(tree(*((x->left))), tree(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(tree_reach(*((x->left))), tree_reach(*((x->right))))))), @_vcc_oset_disjoint(tree_reach(*((x->left))), tree_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree($s, $phys_ptr_cast(P#x, ^t_node)) == (F#tree($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && F#tree($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && !$oset_in($phys_ptr_cast(P#x, ^t_node), $oset_union(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)))) && $oset_disjoint(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(tree_reach(*((x->left))), tree_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_reach($s, $phys_ptr_cast(P#x, ^t_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^t_node)), $oset_union(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
        // assume ==(tree_lsize(x), tree_size(*((x->left)))); 
        assume F#tree_lsize($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_order(x), *((x->key)))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_order($s, $phys_ptr_cast(P#x, ^t_node)) == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node));
        // assume ==(tree_rsize(x), tree_size(*((x->right)))); 
        assume F#tree_rsize($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_size(x), +(+(tree_size(*((x->left))), tree_size(*((x->right)))), 1))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_size($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + F#tree_size($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1;
        // int32_t n3; 
        // int32_t n2; 
        // int32_t n1; 
        // _math \state _dryad_S0; 
        // _dryad_S0 := @_vcc_current_state(@state); 
        SL#_dryad_S0 := $current_state($s);
        // _math \state stmtexpr0#1; 
        // stmtexpr0#1 := _dryad_S0; 
        stmtexpr0#1 := SL#_dryad_S0;
        // non-pure function
        // assert @reads_check_normal((x->left)); 
        assert $thread_local($s, $phys_ptr_cast(P#x, ^t_node));
        // n1 := inorder(*((x->left)), n); 
        call L#n1 := inorder($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node), P#n);
        assume $full_stop_ext(#tok$2^23.12, $s);
        // _math \state _dryad_S1; 
        // _dryad_S1 := @_vcc_current_state(@state); 
        SL#_dryad_S1 := $current_state($s);
        // _math \state stmtexpr1#2; 
        // stmtexpr1#2 := _dryad_S1; 
        stmtexpr1#2 := SL#_dryad_S1;
        // assume ==>(@_vcc_ptr_neq_null(x), ==(intree(x), &&(&&(&&(&&(&&(intree(*((x->left))), intree(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(intree_reach(*((x->left))), intree_reach(*((x->right))))))), @_vcc_oset_disjoint(intree_reach(*((x->left))), intree_reach(*((x->right))))), ==>(@_vcc_ptr_neq_null(*((x->left))), ==(+(+(tree_order(*((x->left))), tree_rsize(*((x->left)))), 1), *((x->key))))), ==>(@_vcc_ptr_neq_null(*((x->right))), ==(tree_order(*((x->right))), +(+(*((x->key)), tree_lsize(*((x->right)))), 1)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#intree($s, $phys_ptr_cast(P#x, ^t_node)) == (F#intree($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && F#intree($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && !$oset_in($phys_ptr_cast(P#x, ^t_node), $oset_union(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)))) && $oset_disjoint(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) && ($non_null($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) ==> F#tree_order($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + F#tree_rsize($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1 == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node))) && ($non_null($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) ==> F#tree_order($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node)) + F#tree_lsize($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(intree_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(intree_reach(*((x->left))), intree_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#intree_reach($s, $phys_ptr_cast(P#x, ^t_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^t_node)), $oset_union(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree(x), &&(&&(&&(tree(*((x->left))), tree(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(tree_reach(*((x->left))), tree_reach(*((x->right))))))), @_vcc_oset_disjoint(tree_reach(*((x->left))), tree_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree($s, $phys_ptr_cast(P#x, ^t_node)) == (F#tree($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && F#tree($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && !$oset_in($phys_ptr_cast(P#x, ^t_node), $oset_union(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)))) && $oset_disjoint(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(tree_reach(*((x->left))), tree_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_reach($s, $phys_ptr_cast(P#x, ^t_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^t_node)), $oset_union(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
        // assume ==(tree_lsize(x), tree_size(*((x->left)))); 
        assume F#tree_lsize($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_order(x), *((x->key)))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_order($s, $phys_ptr_cast(P#x, ^t_node)) == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node));
        // assume ==(tree_rsize(x), tree_size(*((x->right)))); 
        assume F#tree_rsize($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_size(x), +(+(tree_size(*((x->left))), tree_size(*((x->right)))), 1))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_size($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + F#tree_size($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1;
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, intree_reach(x)))), ==(old(_dryad_S0, intree(x)), old(_dryad_S1, intree(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#intree_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node))) ==> F#intree(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node)) == F#intree(SL#_dryad_S1, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, intree_reach(x)))), ==(old(_dryad_S0, intree_reach(x)), old(_dryad_S1, intree_reach(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#intree_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node))) ==> F#intree_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node)) == F#intree_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, tree_reach(x)))), ==(old(_dryad_S0, tree(x)), old(_dryad_S1, tree(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node)) == F#tree(SL#_dryad_S1, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, tree_reach(x)))), ==(old(_dryad_S0, tree_reach(x)), old(_dryad_S1, tree_reach(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node)) == F#tree_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, tree_reach(x)))), ==(old(_dryad_S0, tree_lsize(x)), old(_dryad_S1, tree_lsize(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree_lsize(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node)) == F#tree_lsize(SL#_dryad_S1, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, tree_reach(x)))), ==(old(_dryad_S0, tree_order(x)), old(_dryad_S1, tree_order(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree_order(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node)) == F#tree_order(SL#_dryad_S1, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, tree_reach(x)))), ==(old(_dryad_S0, tree_rsize(x)), old(_dryad_S1, tree_rsize(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree_rsize(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node)) == F#tree_rsize(SL#_dryad_S1, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, tree_reach(x)))), ==(old(_dryad_S0, tree_size(x)), old(_dryad_S1, tree_size(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree_size(SL#_dryad_S0, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size(SL#_dryad_S1, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, intree_reach(*((x->right)))))), ==(old(_dryad_S0, intree(*((x->right)))), old(_dryad_S1, intree(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#intree_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#intree(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#intree(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, intree_reach(*((x->right)))))), ==(old(_dryad_S0, intree_reach(*((x->right)))), old(_dryad_S1, intree_reach(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#intree_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#intree_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#intree_reach(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, tree_reach(*((x->right)))))), ==(old(_dryad_S0, tree(*((x->right)))), old(_dryad_S1, tree(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, tree_reach(*((x->right)))))), ==(old(_dryad_S0, tree_reach(*((x->right)))), old(_dryad_S1, tree_reach(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_reach(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, tree_reach(*((x->right)))))), ==(old(_dryad_S0, tree_lsize(*((x->right)))), old(_dryad_S1, tree_lsize(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_lsize(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_lsize(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, tree_reach(*((x->right)))))), ==(old(_dryad_S0, tree_order(*((x->right)))), old(_dryad_S1, tree_order(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_order(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_order(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, tree_reach(*((x->right)))))), ==(old(_dryad_S0, tree_rsize(*((x->right)))), old(_dryad_S1, tree_rsize(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_rsize(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_rsize(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, tree_reach(*((x->right)))))), ==(old(_dryad_S0, tree_size(*((x->right)))), old(_dryad_S1, tree_size(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_size(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_size(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume <(n1, 2147483647); 
        assume L#n1 < 2147483647;
        // _math \state _dryad_S2; 
        // _dryad_S2 := @_vcc_current_state(@state); 
        SL#_dryad_S2 := $current_state($s);
        // _math \state stmtexpr2#3; 
        // stmtexpr2#3 := _dryad_S2; 
        stmtexpr2#3 := SL#_dryad_S2;
        // assert @prim_writes_check((x->key)); 
        assert $writable_prim($s, #wrTime$2^5.3, $dot($phys_ptr_cast(P#x, ^t_node), t_node.key));
        // *(x->key) := n1; 
        call $write_int(t_node.key, $phys_ptr_cast(P#x, ^t_node), L#n1);
        assume $full_stop_ext(#tok$2^26.3, $s);
        // _math \state _dryad_S3; 
        // _dryad_S3 := @_vcc_current_state(@state); 
        SL#_dryad_S3 := $current_state($s);
        // _math \state stmtexpr3#4; 
        // stmtexpr3#4 := _dryad_S3; 
        stmtexpr3#4 := SL#_dryad_S3;
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, intree_reach(*((x->left)))))), ==(old(_dryad_S2, intree(*((x->left)))), old(_dryad_S3, intree(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#intree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#intree(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#intree(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, intree_reach(*((x->left)))))), ==(old(_dryad_S2, intree_reach(*((x->left)))), old(_dryad_S3, intree_reach(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#intree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#intree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#intree_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->left)))))), ==(old(_dryad_S2, tree(*((x->left)))), old(_dryad_S3, tree(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->left)))))), ==(old(_dryad_S2, tree_reach(*((x->left)))), old(_dryad_S3, tree_reach(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->left)))))), ==(old(_dryad_S2, tree_lsize(*((x->left)))), old(_dryad_S3, tree_lsize(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_lsize(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_lsize(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->left)))))), ==(old(_dryad_S2, tree_order(*((x->left)))), old(_dryad_S3, tree_order(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_order(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_order(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->left)))))), ==(old(_dryad_S2, tree_rsize(*((x->left)))), old(_dryad_S3, tree_rsize(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_rsize(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_rsize(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->left)))))), ==(old(_dryad_S2, tree_size(*((x->left)))), old(_dryad_S3, tree_size(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_size(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_size(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, intree_reach(*((x->right)))))), ==(old(_dryad_S2, intree(*((x->right)))), old(_dryad_S3, intree(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#intree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#intree(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#intree(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, intree_reach(*((x->right)))))), ==(old(_dryad_S2, intree_reach(*((x->right)))), old(_dryad_S3, intree_reach(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#intree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#intree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#intree_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->right)))))), ==(old(_dryad_S2, tree(*((x->right)))), old(_dryad_S3, tree(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->right)))))), ==(old(_dryad_S2, tree_reach(*((x->right)))), old(_dryad_S3, tree_reach(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_reach(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->right)))))), ==(old(_dryad_S2, tree_lsize(*((x->right)))), old(_dryad_S3, tree_lsize(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_lsize(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_lsize(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->right)))))), ==(old(_dryad_S2, tree_order(*((x->right)))), old(_dryad_S3, tree_order(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_order(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_order(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->right)))))), ==(old(_dryad_S2, tree_rsize(*((x->right)))), old(_dryad_S3, tree_rsize(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_rsize(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_rsize(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S2, tree_reach(*((x->right)))))), ==(old(_dryad_S2, tree_size(*((x->right)))), old(_dryad_S3, tree_size(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_size(SL#_dryad_S2, $rd_phys_ptr(SL#_dryad_S2, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_size(SL#_dryad_S3, $rd_phys_ptr(SL#_dryad_S3, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==(old(_dryad_S2, intree_reach(x)), old(_dryad_S3, intree_reach(x))); 
        assume F#intree_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^t_node)) == F#intree_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^t_node));
        // assume ==(old(_dryad_S2, tree(x)), old(_dryad_S3, tree(x))); 
        assume F#tree(SL#_dryad_S2, $phys_ptr_cast(P#x, ^t_node)) == F#tree(SL#_dryad_S3, $phys_ptr_cast(P#x, ^t_node));
        // assume ==(old(_dryad_S2, tree_reach(x)), old(_dryad_S3, tree_reach(x))); 
        assume F#tree_reach(SL#_dryad_S2, $phys_ptr_cast(P#x, ^t_node)) == F#tree_reach(SL#_dryad_S3, $phys_ptr_cast(P#x, ^t_node));
        // assume ==(old(_dryad_S2, tree_lsize(x)), old(_dryad_S3, tree_lsize(x))); 
        assume F#tree_lsize(SL#_dryad_S2, $phys_ptr_cast(P#x, ^t_node)) == F#tree_lsize(SL#_dryad_S3, $phys_ptr_cast(P#x, ^t_node));
        // assume ==(old(_dryad_S2, tree_rsize(x)), old(_dryad_S3, tree_rsize(x))); 
        assume F#tree_rsize(SL#_dryad_S2, $phys_ptr_cast(P#x, ^t_node)) == F#tree_rsize(SL#_dryad_S3, $phys_ptr_cast(P#x, ^t_node));
        // assume ==(old(_dryad_S2, tree_size(x)), old(_dryad_S3, tree_size(x))); 
        assume F#tree_size(SL#_dryad_S2, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size(SL#_dryad_S3, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(intree(x), &&(&&(&&(&&(&&(intree(*((x->left))), intree(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(intree_reach(*((x->left))), intree_reach(*((x->right))))))), @_vcc_oset_disjoint(intree_reach(*((x->left))), intree_reach(*((x->right))))), ==>(@_vcc_ptr_neq_null(*((x->left))), ==(+(+(tree_order(*((x->left))), tree_rsize(*((x->left)))), 1), *((x->key))))), ==>(@_vcc_ptr_neq_null(*((x->right))), ==(tree_order(*((x->right))), +(+(*((x->key)), tree_lsize(*((x->right)))), 1)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#intree($s, $phys_ptr_cast(P#x, ^t_node)) == (F#intree($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && F#intree($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && !$oset_in($phys_ptr_cast(P#x, ^t_node), $oset_union(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)))) && $oset_disjoint(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) && ($non_null($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) ==> F#tree_order($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + F#tree_rsize($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1 == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node))) && ($non_null($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) ==> F#tree_order($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node)) + F#tree_lsize($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_order(x), *((x->key)))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_order($s, $phys_ptr_cast(P#x, ^t_node)) == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node));
        // assert @in_range_i4(+(n1, 1)); 
        assert $in_range_i4(L#n1 + 1);
        // n2 := +(n1, 1); 
        L#n2 := L#n1 + 1;
        // assume <(n2, 2147483647); 
        assume L#n2 < 2147483647;
        // _math \state _dryad_S4; 
        // _dryad_S4 := @_vcc_current_state(@state); 
        SL#_dryad_S4 := $current_state($s);
        // _math \state stmtexpr4#5; 
        // stmtexpr4#5 := _dryad_S4; 
        stmtexpr4#5 := SL#_dryad_S4;
        // non-pure function
        // assert @reads_check_normal((x->right)); 
        assert $thread_local($s, $phys_ptr_cast(P#x, ^t_node));
        // n3 := inorder(*((x->right)), n2); 
        call L#n3 := inorder($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node), L#n2);
        assume $full_stop_ext(#tok$2^31.12, $s);
        // _math \state _dryad_S5; 
        // _dryad_S5 := @_vcc_current_state(@state); 
        SL#_dryad_S5 := $current_state($s);
        // _math \state stmtexpr5#6; 
        // stmtexpr5#6 := _dryad_S5; 
        stmtexpr5#6 := SL#_dryad_S5;
        // assume ==>(@_vcc_ptr_neq_null(x), ==(intree(x), &&(&&(&&(&&(&&(intree(*((x->left))), intree(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(intree_reach(*((x->left))), intree_reach(*((x->right))))))), @_vcc_oset_disjoint(intree_reach(*((x->left))), intree_reach(*((x->right))))), ==>(@_vcc_ptr_neq_null(*((x->left))), ==(+(+(tree_order(*((x->left))), tree_rsize(*((x->left)))), 1), *((x->key))))), ==>(@_vcc_ptr_neq_null(*((x->right))), ==(tree_order(*((x->right))), +(+(*((x->key)), tree_lsize(*((x->right)))), 1)))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#intree($s, $phys_ptr_cast(P#x, ^t_node)) == (F#intree($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && F#intree($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && !$oset_in($phys_ptr_cast(P#x, ^t_node), $oset_union(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)))) && $oset_disjoint(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))) && ($non_null($rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) ==> F#tree_order($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + F#tree_rsize($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1 == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node))) && ($non_null($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) ==> F#tree_order($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node)) + F#tree_lsize($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(intree_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(intree_reach(*((x->left))), intree_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#intree_reach($s, $phys_ptr_cast(P#x, ^t_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^t_node)), $oset_union(F#intree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#intree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree(x), &&(&&(&&(tree(*((x->left))), tree(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(tree_reach(*((x->left))), tree_reach(*((x->right))))))), @_vcc_oset_disjoint(tree_reach(*((x->left))), tree_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree($s, $phys_ptr_cast(P#x, ^t_node)) == (F#tree($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && F#tree($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) && !$oset_in($phys_ptr_cast(P#x, ^t_node), $oset_union(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)))) && $oset_disjoint(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_reach(x), @_vcc_oset_union(@_vcc_oset_singleton(x), @_vcc_oset_union(tree_reach(*((x->left))), tree_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_reach($s, $phys_ptr_cast(P#x, ^t_node)) == $oset_union($oset_singleton($phys_ptr_cast(P#x, ^t_node)), $oset_union(F#tree_reach($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)), F#tree_reach($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node))));
        // assume ==(tree_lsize(x), tree_size(*((x->left)))); 
        assume F#tree_lsize($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_order(x), *((x->key)))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_order($s, $phys_ptr_cast(P#x, ^t_node)) == $rd_inv($s, t_node.key, $phys_ptr_cast(P#x, ^t_node));
        // assume ==(tree_rsize(x), tree_size(*((x->right)))); 
        assume F#tree_rsize($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(tree_size(x), +(+(tree_size(*((x->left))), tree_size(*((x->right)))), 1))); 
        assume $non_null($phys_ptr_cast(P#x, ^t_node)) ==> F#tree_size($s, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size($s, $rd_phys_ptr($s, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + F#tree_size($s, $rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node)) + 1;
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->right)), old(_dryad_S4, intree_reach(x)))), ==(old(_dryad_S4, intree(x)), old(_dryad_S5, intree(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#intree_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node))) ==> F#intree(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node)) == F#intree(SL#_dryad_S5, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->right)), old(_dryad_S4, intree_reach(x)))), ==(old(_dryad_S4, intree_reach(x)), old(_dryad_S5, intree_reach(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#intree_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node))) ==> F#intree_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node)) == F#intree_reach(SL#_dryad_S5, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->right)), old(_dryad_S4, tree_reach(x)))), ==(old(_dryad_S4, tree(x)), old(_dryad_S5, tree(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node)) == F#tree(SL#_dryad_S5, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->right)), old(_dryad_S4, tree_reach(x)))), ==(old(_dryad_S4, tree_reach(x)), old(_dryad_S5, tree_reach(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node)) == F#tree_reach(SL#_dryad_S5, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->right)), old(_dryad_S4, tree_reach(x)))), ==(old(_dryad_S4, tree_lsize(x)), old(_dryad_S5, tree_lsize(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree_lsize(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node)) == F#tree_lsize(SL#_dryad_S5, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->right)), old(_dryad_S4, tree_reach(x)))), ==(old(_dryad_S4, tree_order(x)), old(_dryad_S5, tree_order(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree_order(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node)) == F#tree_order(SL#_dryad_S5, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->right)), old(_dryad_S4, tree_reach(x)))), ==(old(_dryad_S4, tree_rsize(x)), old(_dryad_S5, tree_rsize(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree_rsize(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node)) == F#tree_rsize(SL#_dryad_S5, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->right)), old(_dryad_S4, tree_reach(x)))), ==(old(_dryad_S4, tree_size(x)), old(_dryad_S5, tree_size(x)))); 
        assume !$oset_in($rd_phys_ptr($s, t_node.right, $phys_ptr_cast(P#x, ^t_node), ^t_node), F#tree_reach(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node))) ==> F#tree_size(SL#_dryad_S4, $phys_ptr_cast(P#x, ^t_node)) == F#tree_size(SL#_dryad_S5, $phys_ptr_cast(P#x, ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S4, intree_reach(*((x->left)))))), ==(old(_dryad_S4, intree(*((x->left)))), old(_dryad_S5, intree(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#intree_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#intree(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#intree(SL#_dryad_S5, $rd_phys_ptr(SL#_dryad_S5, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S4, intree_reach(*((x->left)))))), ==(old(_dryad_S4, intree_reach(*((x->left)))), old(_dryad_S5, intree_reach(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#intree_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#intree_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#intree_reach(SL#_dryad_S5, $rd_phys_ptr(SL#_dryad_S5, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S4, tree_reach(*((x->left)))))), ==(old(_dryad_S4, tree(*((x->left)))), old(_dryad_S5, tree(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree(SL#_dryad_S5, $rd_phys_ptr(SL#_dryad_S5, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S4, tree_reach(*((x->left)))))), ==(old(_dryad_S4, tree_reach(*((x->left)))), old(_dryad_S5, tree_reach(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_reach(SL#_dryad_S5, $rd_phys_ptr(SL#_dryad_S5, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S4, tree_reach(*((x->left)))))), ==(old(_dryad_S4, tree_lsize(*((x->left)))), old(_dryad_S5, tree_lsize(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_lsize(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_lsize(SL#_dryad_S5, $rd_phys_ptr(SL#_dryad_S5, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S4, tree_reach(*((x->left)))))), ==(old(_dryad_S4, tree_order(*((x->left)))), old(_dryad_S5, tree_order(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_order(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_order(SL#_dryad_S5, $rd_phys_ptr(SL#_dryad_S5, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S4, tree_reach(*((x->left)))))), ==(old(_dryad_S4, tree_rsize(*((x->left)))), old(_dryad_S5, tree_rsize(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_rsize(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_rsize(SL#_dryad_S5, $rd_phys_ptr(SL#_dryad_S5, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S4, tree_reach(*((x->left)))))), ==(old(_dryad_S4, tree_size(*((x->left)))), old(_dryad_S5, tree_size(*((x->left)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^t_node), F#tree_reach(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node))) ==> F#tree_size(SL#_dryad_S4, $rd_phys_ptr(SL#_dryad_S4, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node)) == F#tree_size(SL#_dryad_S5, $rd_phys_ptr(SL#_dryad_S5, t_node.left, $phys_ptr_cast(P#x, ^t_node), ^t_node));
        // assume <(n3, 2147483647); 
        assume L#n3 < 2147483647;
        // return n3; 
        $result := L#n3;
        assume true;
        assert $position_marker();
        goto #exit;
    }

  anon4:
    // skip

  #exit:
}



const unique l#public: $label;

const unique #tok$2^31.12: $token;

const unique #tok$2^26.3: $token;

const unique #tok$2^23.12: $token;

const unique #tok$3^0.0: $token;

const unique #file^?3Cno?20file?3E: $token;

axiom $file_name_is(3, #file^?3Cno?20file?3E);

const unique #tok$2^5.3: $token;

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Ctraverse?2Dtree?5Ctraverse?2Dinorder.c: $token;

axiom $file_name_is(2, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Ctraverse?2Dtree?5Ctraverse?2Dinorder.c);

const unique #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Ctraverse?2Dtree?5Cdryad_intree.h: $token;

axiom $file_name_is(1, #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Ctraverse?2Dtree?5Cdryad_intree.h);

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^t_node);
