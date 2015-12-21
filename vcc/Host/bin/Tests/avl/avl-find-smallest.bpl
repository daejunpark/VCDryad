axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

const unique ^$##thread_id: $ctype;

axiom $def_math_type(^$##thread_id);

type $##thread_id;

const unique ^$##club: $ctype;

axiom $def_math_type(^$##club);

type $##club;

const unique ^a_node: $ctype;

axiom $is_span_sequential(^a_node);

axiom $def_struct_type(^a_node, 24, false, false);

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2(#s1, #s2, #p, ^a_node) } $inv2(#s1, #s2, #p, ^a_node) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2_without_lemmas(#s1, #s2, #p, ^a_node) } $inv2_without_lemmas(#s1, #s2, #p, ^a_node) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall p: $ptr, q: $ptr, s: $state :: { $in(q, $composite_extent(s, p, ^a_node)) } $in(q, $composite_extent(s, p, ^a_node)) == (q == p));

const unique a_node.left: $field;

axiom $def_phys_field(^a_node, a_node.left, $ptr_to(^a_node), false, 0);

const unique a_node.right: $field;

axiom $def_phys_field(^a_node, a_node.right, $ptr_to(^a_node), false, 8);

const unique a_node.key: $field;

axiom $def_phys_field(^a_node, a_node.key, ^^i4, false, 16);

const unique a_node.height: $field;

axiom $def_phys_field(^a_node, a_node.height, ^^i4, false, 20);

const unique ^$#_purecall_handler#1: $ctype;

axiom $def_fnptr_type(^$#_purecall_handler#1);

type $#_purecall_handler#1;

const unique ^$#_invalid_parameter_handler#2: $ctype;

axiom $def_fnptr_type(^$#_invalid_parameter_handler#2);

type $#_invalid_parameter_handler#2;

const unique ^$#avl_find_smallest.c..36261#3: $ctype;

axiom $def_fnptr_type(^$#avl_find_smallest.c..36261#3);

type $#avl_find_smallest.c..36261#3;

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

function F#avl(#s: $state, SP#root: $ptr) : bool;

const unique cf#avl: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#avl(#s, SP#root) } 1 < $decreases_level ==> $is_null($phys_ptr_cast(SP#root, ^a_node)) ==> F#avl(#s, SP#root));

axiom $function_arg_type(cf#avl, 0, ^^bool);

axiom $function_arg_type(cf#avl, 1, $ptr_to(^a_node));

procedure avl(SP#root: $ptr) returns ($result: bool);
  ensures $is_null($phys_ptr_cast(SP#root, ^a_node)) ==> $result;
  free ensures $result == F#avl($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#avl_reach(#s: $state, SP#root: $ptr) : $oset;

const unique cf#avl_reach: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#avl_reach(#s, SP#root) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#root, ^a_node)) ==> $oset_in($phys_ptr_cast(SP#root, ^a_node), F#avl_reach(#s, SP#root))) && ($is_null($phys_ptr_cast(SP#root, ^a_node)) ==> F#avl_reach(#s, SP#root) == $oset_empty()));

axiom $function_arg_type(cf#avl_reach, 0, ^$#oset);

axiom $function_arg_type(cf#avl_reach, 1, $ptr_to(^a_node));

procedure avl_reach(SP#root: $ptr) returns ($result: $oset);
  ensures $non_null($phys_ptr_cast(SP#root, ^a_node)) ==> $oset_in($phys_ptr_cast(SP#root, ^a_node), $result);
  ensures $is_null($phys_ptr_cast(SP#root, ^a_node)) ==> $result == $oset_empty();
  free ensures $result == F#avl_reach($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#avl_keys(#s: $state, SP#root: $ptr) : $intset;

const unique cf#avl_keys: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#avl_keys(#s, SP#root) } 1 < $decreases_level ==> ($non_null($phys_ptr_cast(SP#root, ^a_node)) ==> $intset_in($rd_inv(#s, a_node.key, $phys_ptr_cast(SP#root, ^a_node)), F#avl_keys(#s, SP#root))) && ($is_null($phys_ptr_cast(SP#root, ^a_node)) ==> F#avl_keys(#s, SP#root) == $intset_empty()));

axiom $function_arg_type(cf#avl_keys, 0, ^$#intset);

axiom $function_arg_type(cf#avl_keys, 1, $ptr_to(^a_node));

procedure avl_keys(SP#root: $ptr) returns ($result: $intset);
  ensures $non_null($phys_ptr_cast(SP#root, ^a_node)) ==> $intset_in($rd_inv($s, a_node.key, $phys_ptr_cast(SP#root, ^a_node)), $result);
  ensures $is_null($phys_ptr_cast(SP#root, ^a_node)) ==> $result == $intset_empty();
  free ensures $result == F#avl_keys($s, SP#root);
  free ensures $call_transition(old($s), $s);



function F#avl_height(#s: $state, SP#root: $ptr) : int;

const unique cf#avl_height: $pure_function;

axiom (forall #s: $state, SP#root: $ptr :: { F#avl_height(#s, SP#root) } 1 < $decreases_level ==> -1 == $unchk_sub(^^i4, 0, 1) ==> ($is_null($phys_ptr_cast(SP#root, ^a_node)) ==> F#avl_height(#s, SP#root) == -1) && ($non_null($phys_ptr_cast(SP#root, ^a_node)) ==> F#avl_height(#s, SP#root) >= 0) && -1 == $unchk_sub(^^i4, 0, 1));

axiom $function_arg_type(cf#avl_height, 0, ^^mathint);

axiom $function_arg_type(cf#avl_height, 1, $ptr_to(^a_node));

procedure avl_height(SP#root: $ptr) returns ($result: int);
  free requires -1 == $unchk_sub(^^i4, 0, 1);
  ensures $is_null($phys_ptr_cast(SP#root, ^a_node)) ==> $result == -1;
  ensures $non_null($phys_ptr_cast(SP#root, ^a_node)) ==> $result >= 0;
  free ensures -1 == $unchk_sub(^^i4, 0, 1);
  free ensures $result == F#avl_height($s, SP#root);
  free ensures $call_transition(old($s), $s);



procedure avl_find_smallest(P#x: $ptr) returns ($result: int);
  requires $non_null($phys_ptr_cast(P#x, ^a_node));
  requires F#avl($s, $phys_ptr_cast(P#x, ^a_node));
  modifies $s, $cev_pc;
  free ensures $in_range_i4($result);
// INV:BEGIN
  ensures $non_null($phys_ptr_cast(P#x, ^a_node));
  ensures F#avl($s, $phys_ptr_cast(P#x, ^a_node));
  ensures F#avl_reach($s, $phys_ptr_cast(P#x, ^a_node)) == F#avl_reach(old($s), $phys_ptr_cast(P#x, ^a_node));
  ensures F#avl_keys($s, $phys_ptr_cast(P#x, ^a_node)) == F#avl_keys(old($s), $phys_ptr_cast(P#x, ^a_node));
  ensures $intset_in($result, F#avl_keys($s, $phys_ptr_cast(P#x, ^a_node)));
// INV:END
  ensures F#avl_height($s, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height(old($s), $phys_ptr_cast(P#x, ^a_node));
  ensures $intset_le_one1($result, F#avl_keys($s, $phys_ptr_cast(P#x, ^a_node)));
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);

// INV:PTR: P#x
// INV:INT: $result
// INV:LST: avl


implementation avl_find_smallest(P#x: $ptr) returns ($result: int)
{
  var stmtexpr1#2: $state;
  var SL#_dryad_S1: $state;
  var stmtexpr0#1: $state;
  var SL#_dryad_S0: $state;
  var L#r: int where $in_range_i4(L#r);
  var stmtexpr1#4: $oset;
  var stmtexpr0#3: $oset;
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
    // assume @decreases_level_is(2147483647); 
    assume 2147483647 == $decreases_level;
    //  --- Dryad annotated function --- 
    // _math \oset _dryad_G0; 
    // _math \oset _dryad_G1; 
    // _dryad_G0 := avl_reach(x); 
    call SL#_dryad_G0 := avl_reach($phys_ptr_cast(P#x, ^a_node));
    assume $full_stop_ext(#tok$3^0.0, $s);
    // _math \oset stmtexpr0#3; 
    // stmtexpr0#3 := _dryad_G0; 
    stmtexpr0#3 := SL#_dryad_G0;
    // _dryad_G1 := _dryad_G0; 
    SL#_dryad_G1 := SL#_dryad_G0;
    // _math \oset stmtexpr1#4; 
    // stmtexpr1#4 := _dryad_G1; 
    stmtexpr1#4 := SL#_dryad_G1;
    // assume ==>(@_vcc_ptr_neq_null(x), ==(avl(x), &&(&&(&&(&&(&&(&&(&&(&&(avl(*((x->left))), avl(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(avl_reach(*((x->left))), avl_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(avl_keys(*((x->left))), avl_keys(*((x->right))))))), @_vcc_oset_disjoint(avl_reach(*((x->left))), avl_reach(*((x->right))))), @_vcc_intset_disjoint(avl_keys(*((x->left))), avl_keys(*((x->right))))), @_vcc_intset_lt_one2(avl_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), avl_keys(*((x->right))))), ||(||(&&(==(avl_height(*((x->left))), avl_height(*((x->right)))), ==(*((x->height)), +(avl_height(*((x->left))), 1))), &&(==(avl_height(*((x->left))), +(avl_height(*((x->right))), 1)), ==(*((x->height)), +(avl_height(*((x->left))), 1)))), &&(==(avl_height(*((x->right))), +(avl_height(*((x->left))), 1)), ==(*((x->height)), +(avl_height(*((x->right))), 1))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl($s, $phys_ptr_cast(P#x, ^a_node)) == (F#avl($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) && F#avl($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) && !$oset_in($phys_ptr_cast(P#x, ^a_node), $oset_union(F#avl_reach($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_reach($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)))) && !$intset_in($rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node)), $intset_union(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)))) && $oset_disjoint(F#avl_reach($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_reach($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) && $intset_disjoint(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) && $intset_lt_one2(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), $rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node))) && $intset_lt_one1($rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) && ((F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) && $rd_inv($s, a_node.height, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1) || (F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1 && $rd_inv($s, a_node.height, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1) || (F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1 && $rd_inv($s, a_node.height, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1)));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(avl_reach(x), @_vcc_oset_union_one1(x, @_vcc_oset_union(avl_reach(*((x->left))), avl_reach(*((x->right))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl_reach($s, $phys_ptr_cast(P#x, ^a_node)) == $oset_union_one1($phys_ptr_cast(P#x, ^a_node), $oset_union(F#avl_reach($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_reach($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), ==(avl_height(x), @ite(>(avl_height(*((x->left))), avl_height(*((x->right)))), +(avl_height(*((x->left))), 1), +(avl_height(*((x->right))), 1)))); 
    assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl_height($s, $phys_ptr_cast(P#x, ^a_node)) == (if F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) > F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) then F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1 else F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1);
    // assume ==>(@_vcc_ptr_neq_null(x), ==(avl_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(avl_keys(*((x->left))), avl_keys(*((x->right))))))); 
    assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl_keys($s, $phys_ptr_cast(P#x, ^a_node)) == $intset_union($intset_singleton($rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node))), $intset_union(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))));
    // assume ==>(@_vcc_ptr_neq_null(x), &&(@_vcc_mutable(@state, x), @writes_check(x))); 
    assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> $mutable($s, $phys_ptr_cast(P#x, ^a_node)) && $top_writable($s, #wrTime$2^5.3, $phys_ptr_cast(P#x, ^a_node));
    // assert @reads_check_normal((x->left)); 
    assert $thread_local($s, $phys_ptr_cast(P#x, ^a_node));
    assume true;
    // if (@_vcc_ptr_eq_null(*((x->left)))) ...
    if ($is_null($rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)))
    {
      anon1:
        // assert @reads_check_normal((x->key)); 
        assert $thread_local($s, $phys_ptr_cast(P#x, ^a_node));
        // return *((x->key)); 
        $result := $rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node));
        assume true;
        assert $position_marker();
        goto #exit;
    }
    else
    {
      anon2:
        // assume ==>(@_vcc_ptr_neq_null(x), ==(avl(x), &&(&&(&&(&&(&&(&&(&&(&&(avl(*((x->left))), avl(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(avl_reach(*((x->left))), avl_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(avl_keys(*((x->left))), avl_keys(*((x->right))))))), @_vcc_oset_disjoint(avl_reach(*((x->left))), avl_reach(*((x->right))))), @_vcc_intset_disjoint(avl_keys(*((x->left))), avl_keys(*((x->right))))), @_vcc_intset_lt_one2(avl_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), avl_keys(*((x->right))))), ||(||(&&(==(avl_height(*((x->left))), avl_height(*((x->right)))), ==(*((x->height)), +(avl_height(*((x->left))), 1))), &&(==(avl_height(*((x->left))), +(avl_height(*((x->right))), 1)), ==(*((x->height)), +(avl_height(*((x->left))), 1)))), &&(==(avl_height(*((x->right))), +(avl_height(*((x->left))), 1)), ==(*((x->height)), +(avl_height(*((x->right))), 1))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl($s, $phys_ptr_cast(P#x, ^a_node)) == (F#avl($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) && F#avl($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) && !$oset_in($phys_ptr_cast(P#x, ^a_node), $oset_union(F#avl_reach($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_reach($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)))) && !$intset_in($rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node)), $intset_union(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)))) && $oset_disjoint(F#avl_reach($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_reach($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) && $intset_disjoint(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) && $intset_lt_one2(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), $rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node))) && $intset_lt_one1($rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) && ((F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) && $rd_inv($s, a_node.height, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1) || (F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1 && $rd_inv($s, a_node.height, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1) || (F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1 && $rd_inv($s, a_node.height, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(avl_reach(x), @_vcc_oset_union_one1(x, @_vcc_oset_union(avl_reach(*((x->left))), avl_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl_reach($s, $phys_ptr_cast(P#x, ^a_node)) == $oset_union_one1($phys_ptr_cast(P#x, ^a_node), $oset_union(F#avl_reach($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_reach($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(avl_height(x), @ite(>(avl_height(*((x->left))), avl_height(*((x->right)))), +(avl_height(*((x->left))), 1), +(avl_height(*((x->right))), 1)))); 
        assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl_height($s, $phys_ptr_cast(P#x, ^a_node)) == (if F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) > F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) then F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1 else F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1);
        // assume ==>(@_vcc_ptr_neq_null(x), ==(avl_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(avl_keys(*((x->left))), avl_keys(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl_keys($s, $phys_ptr_cast(P#x, ^a_node)) == $intset_union($intset_singleton($rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node))), $intset_union(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))));
        // int32_t r; 
        // _math \state _dryad_S0; 
        // _dryad_S0 := @_vcc_current_state(@state); 
        SL#_dryad_S0 := $current_state($s);
        // _math \state stmtexpr0#1; 
        // stmtexpr0#1 := _dryad_S0; 
        stmtexpr0#1 := SL#_dryad_S0;
        // non-pure function
        // assert @reads_check_normal((x->left)); 
        assert $thread_local($s, $phys_ptr_cast(P#x, ^a_node));
        // r := avl_find_smallest(*((x->left))); 
        call L#r := avl_find_smallest($rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node));
        assume $full_stop_ext(#tok$2^20.11, $s);
        // _math \state _dryad_S1; 
        // _dryad_S1 := @_vcc_current_state(@state); 
        SL#_dryad_S1 := $current_state($s);
        // _math \state stmtexpr1#2; 
        // stmtexpr1#2 := _dryad_S1; 
        stmtexpr1#2 := SL#_dryad_S1;
        // assume ==>(@_vcc_ptr_neq_null(x), ==(avl(x), &&(&&(&&(&&(&&(&&(&&(&&(avl(*((x->left))), avl(*((x->right)))), unchecked!(@_vcc_oset_in(x, @_vcc_oset_union(avl_reach(*((x->left))), avl_reach(*((x->right))))))), unchecked!(@_vcc_intset_in(*((x->key)), @_vcc_intset_union(avl_keys(*((x->left))), avl_keys(*((x->right))))))), @_vcc_oset_disjoint(avl_reach(*((x->left))), avl_reach(*((x->right))))), @_vcc_intset_disjoint(avl_keys(*((x->left))), avl_keys(*((x->right))))), @_vcc_intset_lt_one2(avl_keys(*((x->left))), *((x->key)))), @_vcc_intset_lt_one1(*((x->key)), avl_keys(*((x->right))))), ||(||(&&(==(avl_height(*((x->left))), avl_height(*((x->right)))), ==(*((x->height)), +(avl_height(*((x->left))), 1))), &&(==(avl_height(*((x->left))), +(avl_height(*((x->right))), 1)), ==(*((x->height)), +(avl_height(*((x->left))), 1)))), &&(==(avl_height(*((x->right))), +(avl_height(*((x->left))), 1)), ==(*((x->height)), +(avl_height(*((x->right))), 1))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl($s, $phys_ptr_cast(P#x, ^a_node)) == (F#avl($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) && F#avl($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) && !$oset_in($phys_ptr_cast(P#x, ^a_node), $oset_union(F#avl_reach($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_reach($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)))) && !$intset_in($rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node)), $intset_union(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)))) && $oset_disjoint(F#avl_reach($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_reach($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) && $intset_disjoint(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) && $intset_lt_one2(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), $rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node))) && $intset_lt_one1($rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) && ((F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) && $rd_inv($s, a_node.height, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1) || (F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1 && $rd_inv($s, a_node.height, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1) || (F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1 && $rd_inv($s, a_node.height, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1)));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(avl_reach(x), @_vcc_oset_union_one1(x, @_vcc_oset_union(avl_reach(*((x->left))), avl_reach(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl_reach($s, $phys_ptr_cast(P#x, ^a_node)) == $oset_union_one1($phys_ptr_cast(P#x, ^a_node), $oset_union(F#avl_reach($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_reach($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))));
        // assume ==>(@_vcc_ptr_neq_null(x), ==(avl_height(x), @ite(>(avl_height(*((x->left))), avl_height(*((x->right)))), +(avl_height(*((x->left))), 1), +(avl_height(*((x->right))), 1)))); 
        assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl_height($s, $phys_ptr_cast(P#x, ^a_node)) == (if F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) > F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) then F#avl_height($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1 else F#avl_height($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) + 1);
        // assume ==>(@_vcc_ptr_neq_null(x), ==(avl_keys(x), @_vcc_intset_union(@_vcc_intset_singleton(*((x->key))), @_vcc_intset_union(avl_keys(*((x->left))), avl_keys(*((x->right))))))); 
        assume $non_null($phys_ptr_cast(P#x, ^a_node)) ==> F#avl_keys($s, $phys_ptr_cast(P#x, ^a_node)) == $intset_union($intset_singleton($rd_inv($s, a_node.key, $phys_ptr_cast(P#x, ^a_node))), $intset_union(F#avl_keys($s, $rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node)), F#avl_keys($s, $rd_phys_ptr($s, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, avl_reach(x)))), ==(old(_dryad_S0, avl(x)), old(_dryad_S1, avl(x)))); 
        assume !$oset_in($rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node), F#avl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^a_node))) ==> F#avl(SL#_dryad_S0, $phys_ptr_cast(P#x, ^a_node)) == F#avl(SL#_dryad_S1, $phys_ptr_cast(P#x, ^a_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, avl_reach(x)))), ==(old(_dryad_S0, avl_reach(x)), old(_dryad_S1, avl_reach(x)))); 
        assume !$oset_in($rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node), F#avl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^a_node))) ==> F#avl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^a_node)) == F#avl_reach(SL#_dryad_S1, $phys_ptr_cast(P#x, ^a_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, avl_reach(x)))), ==(old(_dryad_S0, avl_height(x)), old(_dryad_S1, avl_height(x)))); 
        assume !$oset_in($rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node), F#avl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^a_node))) ==> F#avl_height(SL#_dryad_S0, $phys_ptr_cast(P#x, ^a_node)) == F#avl_height(SL#_dryad_S1, $phys_ptr_cast(P#x, ^a_node));
        // assume ==>(unchecked!(@_vcc_oset_in(*((x->left)), old(_dryad_S0, avl_reach(x)))), ==(old(_dryad_S0, avl_keys(x)), old(_dryad_S1, avl_keys(x)))); 
        assume !$oset_in($rd_phys_ptr($s, a_node.left, $phys_ptr_cast(P#x, ^a_node), ^a_node), F#avl_reach(SL#_dryad_S0, $phys_ptr_cast(P#x, ^a_node))) ==> F#avl_keys(SL#_dryad_S0, $phys_ptr_cast(P#x, ^a_node)) == F#avl_keys(SL#_dryad_S1, $phys_ptr_cast(P#x, ^a_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, avl_reach(*((x->right)))))), ==(old(_dryad_S0, avl(*((x->right)))), old(_dryad_S1, avl(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^a_node), F#avl_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) ==> F#avl(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, avl_reach(*((x->right)))))), ==(old(_dryad_S0, avl_reach(*((x->right)))), old(_dryad_S1, avl_reach(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^a_node), F#avl_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) ==> F#avl_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_reach(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, avl_reach(*((x->right)))))), ==(old(_dryad_S0, avl_height(*((x->right)))), old(_dryad_S1, avl_height(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^a_node), F#avl_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) ==> F#avl_height(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_height(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node));
        // assume ==>(unchecked!(@_vcc_oset_in(x, old(_dryad_S0, avl_reach(*((x->right)))))), ==(old(_dryad_S0, avl_keys(*((x->right)))), old(_dryad_S1, avl_keys(*((x->right)))))); 
        assume !$oset_in($phys_ptr_cast(P#x, ^a_node), F#avl_reach(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node))) ==> F#avl_keys(SL#_dryad_S0, $rd_phys_ptr(SL#_dryad_S0, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node)) == F#avl_keys(SL#_dryad_S1, $rd_phys_ptr(SL#_dryad_S1, a_node.right, $phys_ptr_cast(P#x, ^a_node), ^a_node));
        // return r; 
        $result := L#r;
        assume true;
        assert $position_marker();
        goto #exit;
    }

  anon4:
    // skip

  #exit:
}



const unique l#public: $label;

const unique #tok$2^20.11: $token;

const unique #tok$3^0.0: $token;

const unique #file^?3Cno?20file?3E: $token;

axiom $file_name_is(3, #file^?3Cno?20file?3E);

const unique #tok$2^5.3: $token;

const unique #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Cavl?5Cavl?2Dfind?2Dsmallest.c: $token;

axiom $file_name_is(2, #file^Z?3A?5CInvariantSynthesis?5CVCDryad?5Cvcc?5CHost?5Cbin?5CTests?5Cavl?5Cavl?2Dfind?2Dsmallest.c);

const unique #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Cavl?5Cdryad_avl.h: $token;

axiom $file_name_is(1, #file^z?3A?5Cinvariantsynthesis?5Cvcdryad?5Cvcc?5Chost?5Cbin?5Ctests?5Cavl?5Cdryad_avl.h);

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^a_node);
