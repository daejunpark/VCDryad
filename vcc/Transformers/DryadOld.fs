
#light
namespace Microsoft.Research.Vcc
    open Microsoft.Research.Vcc
    open Microsoft.Research.Vcc.Util
    open Microsoft.Research.Vcc.TransUtil
    open Microsoft.Research.Vcc.CAST

   // module DryadOld

    (*
    let mkLemmaSkip x y =
        let lemmaName = "LemmaSkip"
        let (isThere, lemmaSkipFunc) = dryadFunDict.TryGetValue(lemmaName)
        if isThere then
            let lemmaSkipExpr = Expr.Call(voidBogusEC(), lemmaSkipFunc, [], [x;y])
            Expr.SpecCode(lemmaSkipExpr)
        else notInDictFail lemmaName *)

    (*    // DEPRECATED: remove after all the new counterparts are in place
    let getLsegs xs =
        let lsegFunName f = f.Name.Contains("lseg")
        let xs' = List.fold (fun acc el -> acc @ (collectCalls el lsegFunName)) [] xs
        let isLsegFun x = match x with Call(_, fn , _, _) -> fn.Name.Contains("lseg") | _ -> false                         
        let getLsegArgs x = match x with Call(_, _, _, args) -> args | _ -> failwith("expected function call")
        let getLsegHdTl args = match args with [hd; tl] -> (peelCast hd, peelCast tl) | _ -> failwith("expected two arguments")
        xs' |> List.filter isLsegFun
            |> List.map getLsegArgs
            |> List.map getLsegHdTl *)

    (* // DEPRECATED:
    let getReqUnPreds vs fpre = 
        let getReqPred v =             
            let isPredParam x = 
                match x with
                | Call(_, fn, _, args) -> 
                    args.Length = 1 && (isExprRef args.Head) && (getExprRef args.Head) = v
                | _ -> false
            let unaryPreds = getUnaryDryadPreds fpre
            unaryPreds |> List.filter isPredParam
        vs |> List.map getReqPred
            |> List.map (fun x -> x |> List.map getFunFromCall) //if x.IsSome then Some(getFunFromCall x.Value) else None) *)

    (* // DEPRECATED: does not take into account field dereferencing
    let getEnsUnPred xs = 
        let getResPred x =
            match x with
            | Call(_, fn, _, args) ->                        
                assert (fn.RetType = Type.Bool && args.Length = 1)
                let arg = args.Head
                match arg with
                | Result _ -> Some fn
                | _ -> None
            | _ -> None
        getUnaryDryadPreds xs |> List.map getResPred 
                            |> List.filter (fun x -> x.IsSome)
                            |> List.map (fun x -> x.Value) *)

    (* // DEPRECATED: does not take into account the field dereferencing            
    let getReqBinPreds vs fpre =
        let aux x = 
            match x with
            | Call(_, fn, _, args) -> 
                let ind1 = List.findIndex(fun x -> x = getExprRef args.Head) vs
                let ind2 = List.findIndex(fun x -> x = getExprRef args.Tail.Head) vs
                (fn.Name, (ind1, ind2))
            | _ -> failwith "[getReqBinPreds] Call expression expected."
        getBinaryDryadPreds fpre 
            |> List.filter allCallArgsAreRefs
            |> List.map aux                *)

    (*
    let mkLsegCall x y =
        let funName = "_dryad_lseg"
        let (isThere, lsegFun) = dryadFunDict.TryGetValue(funName)
        if isThere then
            let lsegFunExpr = Expr.Call(boolBogusEC(), lsegFun, [], [x; y])
            Expr.MkAssert(lsegFunExpr)
        else notInDictFail funName     *)

    (* old list segment manipulations - replaced with more general functions 
    let mkUnfoldLsegFld hd tl = 
        let funName = "_dryad_unfoldAllLseg"
        let (isThere, unfoldAllFunc) = dryadFunDict.TryGetValue(funName)
        if (isThere) then
            let unfoldAllExpr = Expr.Call(boolBogusEC(), unfoldAllFunc, [], 
                                        [(Expr.Cast({bogusEC with Type = ObjectT}, CheckedStatus.Checked, mkRef hd));
                                        (Expr.Cast({bogusEC with Type = ObjectT}, CheckedStatus.Checked, Expr.Deref({bogusEC with Type = ObjectT}, tl)))])
            Expr.MkAssume(unfoldAllExpr)
        else notInDictFail funName
    // DEPRECATED
    let mkUnfoldLseg hd tl =
        let funName = "_dryad_unfoldAllLseg"
        let (isThere, unfoldAllFunc) = dryadFunDict.TryGetValue(funName)
        if isThere then 
            let unfoldAllExpr = Expr.Call(boolBogusEC(), unfoldAllFunc, [], 
                                        [(Expr.Cast({bogusEC with Type = ObjectT}, CheckedStatus.Checked, hd));
                                        (Expr.Cast({bogusEC with Type = ObjectT}, CheckedStatus.Checked, tl))])
            Expr.MkAssume(unfoldAllExpr)
        else notInDictFail funName *)


    (* old version - replaced with a more general code
    let mkMaintAcross dloc locs preState postState =
        let funName = "_dryad_maintainsAcross"
        let (isThere, maintDisjFun) = dryadFunDict.TryGetValue(funName)
        if isThere then 
            let locs' = List.filter(fun x -> x <> dloc) locs
            locs' |> List.map(fun x -> Expr.MkAssume(Expr.Call(boolBogusEC(), maintDisjFun, [], [(mkRef dloc); (mkRef x); (mkRef preState); (mkRef postState)])))
        else [notInDictFail funName] *)
   
    (* old version of maintaining across the list segment
    let mkMaintAcrossLseg loc segs preState postState =
        let funName = "_dryad_maintainsAcrossLseg"
        let (isThere, maintFun) = dryadFunDict.TryGetValue(funName)
        if (isThere) then
            segs |> List.map(fun (p1, p2) -> Expr.MkAssume(Expr.Call(boolBogusEC(), maintFun, [], [(mkRef loc); p1; p2; (mkRef preState); (mkRef postState)])))
        else [notInDictFail funName] *)


    (* old version [from handling the Call expression]
    let reqenv = getReqUnPreds ptrFormals fn.Requires
    let ptrArgReachSets = (List.zip ptrActuals reqenv) 
                            |> List.map (fun (exp, funOpt) -> if funOpt.IsSome then mkReachCallExp env.tenv funOpt.Value exp
                                                                else mkEmptySet)                                                     
    let globDiffPre = ptrArgReachSets |> List.map (fun x -> mkSetDiffStmt globSetPostRef (mkOldStmt (mkRef preStateVar) x))
    let assumeDisjStmt = globDiffPre  |> List.map (fun x -> Expr.MkAssume(mkSetDisjStmt lhsReachSet x))
    let updateGlobReachStmt = ptrArgReachSets 
                            |> List.map (fun x-> mkSetDiffStmt globSetPostRef (mkOldStmt (mkRef preStateVar) x))
                            |> List.map (fun x-> Expr.SpecCode(Macro(bogusEC, "=", [globSetPostRef; (mkSetUnionStmt lhsReachSet x)])))                                                 
    //let expandedReqenv = (List.zip ptrActuals reqenv) |> List.collect (fun (p, fs) -> [for f in fs -> (p, f)])
    //let argsReachSet = createReachSetUnion env.tenv (matchAndExpand ptrActuals reqenv)    
    *)

   (* FIXME: this is obsolete
    if (not lsegs.IsEmpty) then
        let actuals = args |> List.map getExprRef
        let f2a = Map.ofList(List.zip fn.Parameters actuals)
        let getVarPairs ps = 
            match ps with
            | (Ref(_, vpr1), Ref(_, vpr2)) -> (mkRef f2a.[vpr1], mkRef f2a.[vpr2])
            | (Ref(_, vpr1), Result(_)) -> (mkRef f2a.[vpr1], mkRef varLhs)          
            | (Result(_), Ref(_, vpr2)) -> (mkRef varLhs, mkRef f2a.[vpr2])
            | (pr1, pr2) -> failwith("[getVarPairs in call handling]expected a pair of Refs " + pr2.ToStringWT(true))
        env.ltups @ (List.map (fun x -> getVarPairs x) lsegs)
    else
        env.ltups
  *)

    

    (* location pred
        let getLocPredMap xs =
            let getLocPredPr x = 
                match x with
                | Call(_, fn, _, args) ->
                    assert (fn.RetType = Type.Bool && args.Length = 1)
                    let loc = getExprRef args.Head
                    (loc, fn)
                | _ -> failwith "Expected a Call expression"                    
            getUnaryPreds xs
                |> List.map (fun x -> getLocPredPr x)
                |> Map.ofList 
    -- end of location pred *)

    (* add comments mapper function
        let rec addComments(stmt, env) =
            let aux assignType denv strcnt =
                match assignType with
                | Simple(_) -> ([Comment(bogusEC, "simple assignment " + strcnt)], denv)
                | FieldLoad(_) -> ([Comment(bogusEC, "load field " + strcnt)], denv)
                | FieldStore(varLhs, _, _) -> 
                    let denv' = if (List.exists (fun x -> x = varLhs) denv) then denv else varLhs::denv
                    let derefs = List.foldBack(fun (x:Variable) acc -> x.Name::acc) denv' []
                    ([Comment(bogusEC, "store assignment " + strcnt) ;
                        Comment(bogusEC, "derefs: " + (derefs.ToString()))], denv')
                | FunCall(_) -> 
                    // TODO: analyze args
                    ([Comment(bogusEC, "call assignment " + strcnt)], denv)
            match stmt with
            | VarDecl(_, v, _) as vs -> 
                if (v.Type.IsPtr && not(List.exists (fun x -> x = v) env.lenv)) then 
                    let lenv' = v::env.lenv
                    let locs = List.foldBack (fun (x : Variable) acc -> x.Name :: acc) lenv' []
                    let locComment = Comment(bogusEC, "locs: " + (locs.ToString()))
                    (Expr.MkBlock(vs :: [locComment]), {env with lenv = lenv'})
                else
                    (vs, env)
            | Macro(ec, "=", [lhs; rhs]) as assign ->
                let assignType = findAssignType (peelCast lhs) (peelCast rhs)
                let (xstmts, denv') = aux assignType env.denv (env.cnt.ToString())
                (Expr.MkBlock(assign::xstmts), { env with denv = denv'; cnt = env.cnt + 2})
            | Block(ec, es, bc) -> 
                let stmts' = mapRecEnv env addComments es
                (Block(ec, stmts', bc), env)
            | If(ec, tc, cond, te, ee) ->
                // TODO: analyze cond for dereferencing
                let (te', _) = addComments(te, env)
                let (ee', _) = addComments(ee, env)
                (If(ec, tc, cond, te', ee'), env)
            | Macro(ec, "while", [linv; lcond; lbody]) ->
                // TODO: analyze lcond for dereferencing
                let (lbody', _) = addComments(lbody, env)
                (Macro(ec, "while", [linv; lcond; lbody']), env)
            | _  as s -> 
                //let dummyComment = Comment(bogusEC, "Dummy comment")
                (s, env)
    -- end of add comments mapper function *)



    (* internal function stuff - for now OBSOLETE
        let addInternalFunctions decls =
            printfn "[Dryad phase 0] begin"
            let name2Fn = new Dict<_,_>()
            for d in decls do
                match d with 
                | Top.FunctionDecl h -> name2Fn.[h.Name] <- h
                | _ -> ()

        let reachSet =
            let rootVar = Variable.CreateUnique "root" Type.ObjectT VarKind.Parameter
            let rootVarRef = Ref({ bogusEC with Type = Type.ObjectT }, rootVar) 
            let voidPtrBogusEC () = { bogusEC with Type = PhysPtr(Void) }
            let nullExpr = Cast(voidPtrBogusEC(), CheckedStatus.Checked, IntLiteral(intBogusEC(), bigint(0)))
            let resultExpr = Result({ bogusEC with Type = Type.PtrSet})
            let ptrsetEC = { bogusEC with Type = Type.PtrSet }
            let emptySetExpr = Expr.Macro (ptrsetEC, "_vcc_set_empty", [])
            let universeSetExpr = Expr.Macro(ptrsetEC, "_vcc_set_universe", [])
            let setInFunc = 
                { Function.Empty() with 
                    IsSpec = true
                    Name = "_vcc_set_in"
                    RetType = Type.PtrSet
                }

            //let emptySetExpr = Macro({ bogusEC with Type = Type.PtrSet}, "set", [])
            Top.FunctionDecl (
                {   Function.Empty() with 
                        IsSpec  = true
                        Name    = "_vcc_dryad_reach_set"
                        //Reads   = [Call(bogusEC, name2Fn.["_vcc_set_universe"], [], [])]
                        Reads = [universeSetExpr]
                        RetType = Type.PtrSet
                        Parameters = [rootVar]
                        Ensures = [mkImpl (mkEq rootVarRef nullExpr) (mkEq resultExpr emptySetExpr)] 
                                @ [mkImpl (mkNot(mkEq rootVarRef nullExpr)) (Call({bogusEC with Type = Type.PtrSet}, setInFunc, [], [rootVarRef; resultExpr]))]                            
                }
            )

        let reachSetStr = reachSet.ToString()
        printf " created function declaration: \n %s"  reachSetStr
        printfn "[Dryad phase 0] end"
        let specAndRests, regularFuncs = List.partition specAndRest decls
        specAndRests @ [reachSet] @ regularFuncs

        //helper.AddTransformer("dryad-add-defs", TransHelper.Decl addInternalFunctions)
    -- end of addInternalFunctions decls *)


    (* axiom related - OBSOLETE for now     
        // helper function
        let printAxioms decls =
            for d in decls do
                match d with
                | Top.Axiom ax ->
                    match ax with 
                    | Quant(_, qd) -> 
                        printfn "Quantified data :"
                        let quantKindStr qk =
                            match qk with
                            | Forall -> "forall "
                            | Exists -> "exists "
                            | Lambda -> "lambda "
                        printfn " quantType: %s " (quantKindStr qd.Kind)
                        printf  " quantVars: " 
                        List.iter (fun (v : Variable) -> printf "var(%s)" v.Name) qd.Variables
                        printfn ""
                        if qd.Condition.IsSome then printf " quantCond: %s" (qd.Condition.Value.ToString())
                        printfn " quantBody: %s" (qd.Body.ToString())
                    | _ -> ()
                | _ -> ()

        let addAxioms decls =
            let ptrsetEC = { bogusEC with Type = Type.PtrSet }
            let varOs1 = Variable.CreateUnique "os1" Type.PtrSet VarKind.QuantBound 
            let refOs1 = mkRef varOs1
            let varOs2 = Variable.CreateUnique "os2" Type.PtrSet VarKind.QuantBound
            let refOs2 = mkRef varOs2
            let universeSetExpr = Expr.Macro(ptrsetEC, "_vcc_set_universe", [])
            let disjointSetExpr = Expr.Macro(boolBogusEC(), "_vcc_set_disjoint", [refOs1; refOs2])
            let differenceSetExpr = Expr.Macro(ptrsetEC, "_vcc_set_difference", [universeSetExpr; refOs2])
            let subsetSetExpr = Expr.Macro(boolBogusEC(), "_vcc_set_subset", [refOs1; differenceSetExpr])
            let disjointnessAxiom =  
                Top.Axiom(Quant(boolBogusEC(), ({Kind = QuantKind.Forall ; Variables = [varOs1 ; varOs2] ; 
                                                Triggers = []; Condition = None ; Body = mkEq disjointSetExpr subsetSetExpr ; Weight = "" })))
            //printf " added axiom: \n %s" (disjointnessAxiom.ToString())
            //printfn "[Dryad phase 1] end"
            //printAxioms decls
            let specsAndRest, regularFuncs = List.partition specAndRest decls
            specsAndRest @ [disjointnessAxiom] @ regularFuncs

         helper.AddTransformer("dryad-add-axioms", TransHelper.Decl addAxioms)
    -- end of axiom related comment *)

    (* _dryad_ stuff
        let firstToUpper (s : string) = 
            let firstCharUpper = System.Char.ToUpper(s.Chars(0))
            let restBase = s.ToCharArray()
            Array.set restBase 0 firstCharUpper
            System.String.Concat(restBase)
        let dryadBaseName dryadFun = 
            assert (dryadFun.Name.StartsWith("_dryad_"))
            dryadFun.Name.Substring(7)                
        let preToReachPred e =
            match e with
            | Call(_, fn, _, [x]) -> 
                if (fn.Name.StartsWith("_dryad_") && x.Type.IsPtr) then 
                    let reachFunName = fn.Name + "_N"                                                            
                    let reachFunUnfoldName = "_dryad_" + "unfold" + (firstToUpper (dryadBaseName fn)) + "N"
                    let (isOk, reachFun) = dryadFunDict.TryGetValue(reachFunName)
                    if (isOk) then 
                        let (isOk', unfoldFun) = dryadFunDict.TryGetValue(reachFunUnfoldName)
                        printfn "x: %s reach: %s" (x.ToString()) (reachFun.ToString())
                        if (isOk') then 
                        let td = getTypeDecl x
                        let ptrFields = td.Fields |> (List.filter (fun x -> x.Type.IsPtr))
                        printfn "td: %s" (ptrFields.ToString())
                        let ptrSubexpr = ptrFields |> List.filter (fun y -> unfoldFun.Ensures.Head.HasSubexpr(fun z -> match z with Expr.Dot(_, _, fld) when fld = y -> true | _ -> false))
                        printfn "ptrSubexpr: %s" (ptrSubexpr.ToString())
                        printfn "unfoldFun: %s" (unfoldFun.ToString()) 
                    else printfn "Appropriate unfold not found."
                    else 
                    printfn "WARNING: fun %s (%s) called, but no reach fun [%s] found." fn.Name (x.ToString()) reachFunName
            | _ -> ()//failwith("preToReachPred default not implemented")                    
    -- end of _dryad_stuff *)
