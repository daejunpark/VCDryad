#light

namespace Microsoft.Research.Vcc
    open Microsoft.Research.Vcc
    open Microsoft.Research.Vcc.Util
    open Microsoft.Research.Vcc.TransUtil
    open Microsoft.Research.Vcc.CAST

    module Dryad = 
        let dryadFunDict = new Dict<string, Function>()
        let dryadGlobVarDict = new Dict<string, Variable>()

        // generic helper functions
        let list2Tuple xs =
            match xs with
            | [hd; tl] -> (hd, tl)
            | _ -> failwith "[list2Tuple] Expected a list with exactly two elems."

        // ---------------------------------------------------------------------------------------------------
        // common vcc macros
        let mkCheckedCastExpr ty x = Expr.Cast({bogusEC with Type = ty}, CheckedStatus.Checked, x)
        let mkDerefExpr x f =
            let dotExpr = Expr.MkDot(mkRef x, f)
            let fldEC = {bogusEC with Type = f.Type}
            Expr.Deref(fldEC, dotExpr)
        let mkOldStmt (state : Expr) (value : Expr) = Expr.Old(value.Common, state, value)
        //let mkEmptySet = Expr.Macro ({ bogusEC with Type = Type.PtrSet }, "_vcc_set_empty", [])
        //let mkEmptySet = Expr.Macro ({ bogusEC with Type = Type.PtrSet }, "_vcc_set_empty", [])
        let mkAtStmt (state : Expr) (value: Expr) = Expr.Macro(value.Common, "_vcc_in_state", [state; value])
        //let mkSetDiffStmt  (e1 : Expr) (e2 : Expr) = Expr.Macro(e1.Common, "_vcc_set_difference", [e1; e2])
        //let mkSetDisjStmt  (e1 : Expr) (e2 : Expr) = Expr.Macro(boolBogusEC(), "_vcc_set_disjoint", [e1; e2])

        //let mkSetUnionStmt (e1 : Expr) (e2 : Expr) = Expr.Macro(e1.Common, "_vcc_set_union", [e1; e2])
        //let mkSetSingleton (e1 : Expr)             = Expr.Macro(e1.Common, "_vcc_set_singleton", [e1])
        //let mkEquivStmt (x : Expr) (y : Expr) = Expr.Macro(boolBogusEC(), "==", [x; y])


        // CAST related extractors and testers
        let rec getTypeRef t = 
            match t with 
            | Type.Ref(td) -> td
            | Type.PhysPtr(tp) -> getTypeRef tp
            | _ -> failwith ("Expected Ref type, got " + (t.ToString()))

        let isTypeDecl (x : Expr) = 
          match x.Type with 
          | Type.PhysPtr(pt) -> match pt with Type.Ref(td) -> true | _ -> false
          | _ -> false

        
        let getTypeDecl (x : Variable) = 
            match x.Type with 
            | Type.PhysPtr(pt) -> getTypeRef(pt)
            | _ -> failwith "Expected pointer to a structure."  

        let getTypeDeclFld (f: Field) = getTypeRef f.Type
        let rec getTypeDeclExp (x: Expr) =
            match x with 
            | Deref(_, e)  -> getTypeDeclExp e
            | Dot(_, _, f) -> getTypeDeclFld f
            | Ref(_, v)  -> getTypeDecl v
            | _ -> getTypeRef x.Type
            //| _ -> failwith "[getTypeDeclExp] unhandled expression %s " (x.ToStringWT(true))

        // Expr.Call -> (Function, Expr list)
        // extracts Function and the list of arguments from the call expression
        let getCallFunAndArgs x =
            match x with
            | Call(_, fn, _, args) -> (fn, args)
            | _ -> failwith "[getCallFunAndArgs] Expected a function call Expr"

        let getCallFunArgs x =
            match x with 
            | Call(_, _, _, args) -> args
            | _ -> failwith "[getCallFunArgs] Expected a function call Expr"

        let mkCallExpr ec fn xs =
            Expr.Call(ec, fn, [], xs)
        let mkCallBoolRet fn xs =
            mkCallExpr (boolBogusEC()) fn xs
            //let cxs = xs //|> List.map (mkCheckedCastExpr ObjectT)
            //Expr.Call(boolBogusEC(), fn, [], cxs)

        let mkCallVoidRet fn xs =
            mkCallExpr (voidBogusEC()) fn xs

        // (Expr list) -> (Expr list) -> bool
        // Return true if the lists have the same number of arguments and matching types
        let canMatchParams (vs : Variable list) (xs : Expr list) = 
            vs.Length = xs.Length &&
            List.forall2 (fun v x -> (getTypeDecl v = getTypeDeclExp x)) vs xs

        let canMatchFunPtrParams fn xs = 
            let ptrParams = fn.Parameters |> List.filter (fun x -> x.Type.IsPtr)
            canMatchParams ptrParams xs

        type IntOptionPair = int option * int option
        type FieldListPair = Field list * Field list
        type ParamRetPred = 
            | UnaryPred of Function * int option * Field list
            | BinaryPred of Function * IntOptionPair * FieldListPair

        // analyzeDeref : Expr -> (Variable, Field list)
        // finds the base variable and the sequence of dereferences
        let analyzeDeref x =
            let rec aux e fs = 
                match e with 
                | Deref(_, e') -> aux e' fs
                | Dot(_, e', fld) -> aux e' (fld :: fs)
                | Ref(_, v) -> (Some(v), fs) 
                | Result _ -> (None, fs)
                | _ as exp -> failwith "[analyzeDeref] Unexpected expression %s" (exp.ToString())
            aux x []            

        // printParamRetPred : ParamRetPred -> unit
        // print the content of the param ret pred type
        let printParamRetPred x = 
            let optToStr (x : int option) = if x.IsSome then x.Value.ToString() else "<<result>>"
            match x with
            | UnaryPred(fn, intOpt, fieldList) -> printfn "(fn: %s, paramIdx: %s, fldLst: %s)" fn.Name (optToStr intOpt) (fieldList.ToString())
            | BinaryPred(fn, intOptPair, fsPair) -> 
                let intOpt1, intOpt2 = intOptPair
                let fs1, fs2 = fsPair
                printfn "fn: %s,  paramIdx1: %s fs1: %s, paramIdx2: %s, fs2: %s" fn.Name (optToStr intOpt1) (fs1.ToString()) (optToStr intOpt2) (fs2.ToString())

        // mkParamRetPred : Variable list -> Expr -> ParamRetPred
        // creates parametrized predicate from the call expression
        let mkParamRetPred vs x = 
            // analyzeArg : Expr -> (int option, Field list)
            // extract argument index (Some) or ret value (None) and the list of dereferenced fields
            let analyzeArg e =
                match e with
                | Ref(_, v) ->  
                    let ind = vs |> List.findIndex(fun x -> x = v)
                    (Some(ind), [])
                | Result _ -> (None, [])
                | Deref _ as de -> 
                    let (varOpt, fs) = analyzeDeref de
                    if varOpt.IsSome then 
                        let ind = vs |> List.findIndex(fun x -> x = varOpt.Value)
                        (Some(ind), fs)
                    else (None, fs)
                | _ -> (Some(0), [])
            match x with
            | Call(_, fn, _, args) -> 
                assert(fn.RetType = Type.Bool)
                match args.Length with 
                | 1 ->                
                    let (paramRet, derefFields) = analyzeArg args.Head    
                    UnaryPred(fn, paramRet, derefFields)
                | 2 -> 
                    let (paramRet1, derefFields1) = analyzeArg args.Head
                    let (paramRet2, derefFields2) = analyzeArg args.Tail.Head
                    BinaryPred(fn, (paramRet1, paramRet2), (derefFields1, derefFields2))
                | _ -> failwith "Only 1ary and 2ary predicates  are supported."
            | _ -> failwith "Expecting the Call expression."

        //isUnaryParamRetPred : ParamRetPred -> Bool
        let isUnaryParamRetPred pred = match pred with UnaryPred _ -> true | _ -> false

        // isBinaryParamRetPred : ParamRetPred -> Bool
        let isBinaryParamRetPred pred = match pred with BinaryPred _ -> true | _ -> false

        let untagUnaryParmRetPred x = 
            match x with 
            | UnaryPred(fn, intOpt, derefFields) -> (fn, intOpt, derefFields) 
            | _ -> failwith "Expected UnaryParamRetPred" 

        let untagBinaryParamRetPred x =
            match x with
            | BinaryPred(fn, (paramRet1, paramRet2), (derefFields1, derefFields2)) -> (fn, (paramRet1, paramRet2), (derefFields1, derefFields2))
            | _ -> failwith "Expected BinaryRetPred"


        // isParamPred : ParamRetPred -> Bool
        let isParamPred pred = 
            match pred with
            | UnaryPred (_, intOpt, _) -> intOpt.IsSome
            | BinaryPred(_, (intOpt1, intOpt2), _) -> intOpt1.IsSome && intOpt2.IsSome

        // isRetPred : ParamRetPred -> Bool
        let isRetPred pred = not (isParamPred pred)

        let isRelevantRetPred pred =
            match pred with
            | UnaryPred(_, intOpt, _) -> intOpt.IsNone
            | BinaryPred(_, (intOpt1, intOpt2), _) -> intOpt1.IsNone
        
        type AssignType =
            | Simple of Variable * Variable option
            | FieldStore of Variable * Field * Variable option
            | FieldLoad of Variable * Variable * Field
            | FunCall of Variable * Expr

        // interp. dryad functions and predicates (parametrized by the struct definitions)
        type DryadType = {
            typeDecl   : TypeDecl
            defNames   : string list
            baseDefs   : Map<string, Function>
            unfoldDefs : Map<string, Function>
            sameDefs   : Map<string, Function>
            condDefs   : Map<string, Function>
            disjDefs   : Map<string, Function>
            defDeps    : Map<string, Field list>
            fieldInf   : Map<string, string list>
            reachFun   : Map<string, Function>
            lemmaDefs  : Map<string, Function>
        }
        let defaultDryadType td = { typeDecl = td; 
                                    defNames = []; 
                                    baseDefs = Map.empty; 
                                    unfoldDefs = Map.empty; 
                                    sameDefs = Map.empty; 
                                    condDefs = Map.empty; 
                                    disjDefs = Map.empty;
                                    defDeps = Map.empty; 
                                    fieldInf = Map.empty;
                                    reachFun = Map.empty;    
                                    lemmaDefs = Map.empty } 
        
        let getDryadType (dryadMap: Map<string, DryadType>) (typeDecl : TypeDecl) =
            if dryadMap.TryFind(typeDecl.Name).IsSome then dryadMap.[typeDecl.Name] 
            else failwith ("Type " + typeDecl.Name + " must be defined as a struct.")
        let getFieldType (dryadType: DryadType) (fldName: string) =
            let fields = dryadType.typeDecl.Fields
            fields |> List.find(fun fld -> fld.Name = fldName)
        let notInMapFail funName mapName = failwith(" <" + funName + ">" + " not found in " + mapName)

        type DeclEnv = { // using one filed record here to account for possible extensions
            type2Dryad : Map<string, DryadType>
        }

        let printStrStrsMap str strs             = printfn "  * fld: %5s -> defs: %s" str (strs.ToString())
        let printDryadType s dt = 
            let printStrFunMap s (f : Function)      = printfn "  * def: %5s -> fun:  %s" s f.Name
            let printStrFldsMap s (fs : Field list)  = printfn "  * def: %5s -> flds: %s" s ((fs |> List.fold (fun acc fld -> fld.Name :: acc) []).ToString())
            let printMaps m = (m |> Map.iter (fun str func ->  printStrFunMap str func))
            printfn "dryad type   %s " s
            printfn "typeDecl:    %s" dt.typeDecl.Name
            printfn "defNames:    %s" (dt.defNames.ToString())
            printfn "baseDefs:     "; (dt.baseDefs   |> printMaps)
            printfn "unfoldDefs:   "; (dt.unfoldDefs |> printMaps)
            printfn "sameDefs:     "; (dt.sameDefs   |> printMaps)
            printfn "condDefs:     "; (dt.condDefs   |> printMaps)
            printfn "disjDefs:     "; (dt.disjDefs   |> printMaps)
            //printfn "lemmaDefs:    "; (dt.lemmaDefs  |> printMaps)
            printfn "defDeps:      "; (dt.defDeps    |> Map.iter (fun str flds -> printStrFldsMap str flds))
            printfn "fiedlInf:     "; (dt.fieldInf   |> Map.iter (fun str strs -> printStrStrsMap str strs))
            printfn "reachFun:     "; (dt.reachFun   |> printMaps)

        let printDeclEnv env = 
            printfn " ------------ DECL ENV ---------------"
            let m = env.type2Dryad
            m |> Map.iter (fun s x -> printDryadType s x)
            printfn "--------------------------------------"

        type DryadEnv = {
            curfn  : string                    // current function
            locs   : Variable list             // locations
            dlocs  : Variable list             // dereferenced locs
            lsing  : Expr list                 // unary location epxressions
            ltups  : (Expr * Expr) list        // location tuples
            tenv   : Map<string, DryadType>    // type invariant env
            cnt    : int
            //gdecls : Expr list
            dcnt   : int
        }

        let isFieldModifStmt (e: Expr) = 
            match e with
            | Expr.Macro(_, "=", [Deref(_, Dot(_, Ref(_, _), _));_])
            | Expr.Call (_, { Name = "free" }, _, _) -> true
            | _ -> false

        let rec peelCast e =
            match e with 
            | Cast(_, _, exp) -> peelCast exp
            | _ as ee -> ee

        // ------------------------------------------------------------------------------
        //let globSetPre  = Variable.CreateUnique "_dryad_G0" Type.PtrSet VarKind.SpecLocal
        //let globSetPost = Variable.CreateUnique "_dryad_G1" Type.PtrSet VarKind.SpecLocal

        // FIXME: look-up the global variable in the dictionary
        let globSetPre  = Variable.CreateUnique "_dryad_G0" Type.OSet VarKind.SpecLocal
        let globSetPost = Variable.CreateUnique "_dryad_G1" Type.OSet VarKind.SpecLocal
        let globSetPreRef  = mkRef globSetPre
        let globSetPostRef = mkRef globSetPost

        let notInDictFail funName = 
            //failwith(" <" + funName + ">" + " not found in dryadFunDict!")
            printfn "< %s > not found in dryadFunDict" funName
            Comment(bogusEC, "ERROR: " + funName + " is missing - Dryad transformer might not work.")

        // custom attribute related
        let isAttr key value a = match a with VccAttr(ky, vl) -> ky = key && vl = value | _ -> false
        //let isAnyBoogieAttr a = a = AttrBoogie0
        let isAttrAnyVal key a = match a with VccAttr(ky, _) -> ky = key | _ -> false
        let isDryadAttr value a = isAttr "dryad" value a 
        let isAnyDryadAttr a = isAttrAnyVal "dryad" a 
        let isAnyBoogieAttr a = isAttrAnyVal "_boogie0" a 
        let isPureAttr value a  = isAttr "is_pure" value a
        let tdHasDryadAttr value (td : TypeDecl) = td.CustomAttr |> List.exists(fun x -> isDryadAttr value x)
        let tdHasAnyDryadAttr (td : TypeDecl) = td.CustomAttr |> List.exists(fun x -> isAnyDryadAttr x)
        let funHasDryadAttr value (f : Function) = f.CustomAttr  |> List.exists(fun x -> isDryadAttr value x)
        let funHasAnyDryadAttr (f : Function) = f.CustomAttr  |> List.exists(fun x -> isAnyDryadAttr x)
        let funHasAnyBoogieAttr (f : Function) = f.CustomAttr  |> List.exists(fun x -> isAnyBoogieAttr x)
        let funGetDryadAttr (f: Function) = match (f.CustomAttr |> List.find (isAnyDryadAttr)) with VccAttr(_, v) -> v | _ -> failwith "Expected Dryad attr"
        let funHasPureAttr  value (f : Function) = f.CustomAttr  |> List.exists(fun x -> isPureAttr value x)
        // ----------------------------------------------------------------------------------------------------------
        let isNaryDryadPred n f = 
            let ptrParams = f.Parameters |> List.filter (fun x -> x.Type.IsPtr)
            funHasAnyDryadAttr f && f.RetType = Type.Bool && ptrParams.Length = n 

        let isUnaryDryadPred f  = isNaryDryadPred 1 f
        let isBinaryDryadPred f = isNaryDryadPred 2 f
        let isCondUnaryDryadPred  f = isNaryDryadPred 2 f
        let isCondBinaryDryadPred f = isNaryDryadPred 3 f


        // ----------------------- misc helpers ---------------------------------------

//      | Deref(_, Dot(_, Ref(_, loc), _)) -> dfl @ [loc]
        let isFunIthParamType x i fn = 
            let fnParams = fn.Parameters
            assert (i < fnParams.Length)
            let ith = List.nth fnParams i
            ith.Type = x
        let isFunFirstParamType x fn =
            isFunIthParamType x 0 fn

        let decompRefExpr x =
            match x with
            | Expr.Deref(_, Expr.Dot(_, Expr.Ref(_, loc), fld)) -> (loc, Some(fld))
            | Expr.Ref(_, loc) ->  (loc, None)
            | _ -> failwith ("[decompRefExpr] Expected single deref or ref expr; got" + (x.ToStringWT(true)))
        
        let isResExpr x = 
            match x with
            | Expr.Return _ -> true
            | _ -> false

        let isDotExpr v fld x = 
            match x with 
            | Expr.Dot(_, Expr.Ref(_, v1), fld1) when v1  = v && fld1 = fld -> true 
            | _ -> false

        let getDerefBase x =
            match x with 
            | Deref(_, Dot(_, Ref(_, loc), _)) -> loc
            | _ -> failwith "Exepected a Deref expression"

        let isRefExprVar v x = 
            match x with
            | Ref(_, v') when v = v' -> true
            | _ -> false

        let isExprRef x = 
            match x with
            | Ref(_, v) -> true
            | _ -> false

        let isMallocCall x = 
            match x with
            | Call(_, { Name = "malloc" }, _, _) -> true
            | _ -> false

        let getExprRef x =
            match x with
            | Ref (_, v) -> v
            | _ -> failwith ("Expected expression Ref, got " + (x.ToStringWT(true)))

        let isNullExpr (x : Expr) =
            let bigintZero = bigint(0)
            let isZero (e : Expr) = 
                match e with 
                | Expr.IntLiteral (_, bigintZero) -> true
                | _ -> false             
            x.Type.IsPtr && x.HasSubexpr(isZero)

        let getReachFunOpt (dryadMap: Map<string, DryadType>) (pred: Function) (typeDecl: TypeDecl) =
            let dryadType = getDryadType dryadMap typeDecl
            dryadType.reachFun.TryFind(pred.Name)                
        let mkReachCall (reachFun: Function) (xs : Expr list) = Expr.Call( { bogusEC with Type = Type.OSet }, reachFun, [], xs)            
        let mkReachCallExp (dryadMap: Map<string, DryadType>) (pred : Function) (exp : Expr) = 
            let typeDecl = getTypeDeclExp exp
            let reachFun = getReachFunOpt dryadMap pred typeDecl
            if reachFun.IsSome then mkReachCall reachFun.Value [exp]
            else notInMapFail pred.Name "reachFun" 

        let mkDerefExpInd xs (expOpt : Expr option) (intOpt : int option) (flds: Field list) (ty : Type) = 
            let baseExp = 
                if intOpt.IsSome then List.nth xs intOpt.Value
                else (if expOpt.IsSome then expOpt.Value else Expr.Result({bogusEC with Type = ty}))
            flds |> List.fold (fun acc x -> Deref(acc.Common, Expr.MkDot(acc, x))) baseExp

        let mkExprArgsBin xs exp pred =
            match pred with
            | BinaryPred(fn, intOptPair, fieldListPair) ->
                let (intOpt1, intOpt2) = intOptPair
                let (fieldList1, fieldList2) = fieldListPair
                let dexp1 = mkDerefExpInd xs (Some exp) intOpt1 fieldList1 exp.Type
                let dexp2 = mkDerefExpInd xs (Some exp) intOpt2 fieldList2 exp.Type
                (dexp1, dexp2)
            | _ -> failwith "Expected BinaryPred" 


        let mkCallFromPred xs exp pred =
            match pred with
            | UnaryPred(fn, intOpt, fieldList) -> 
                let dexp = mkDerefExpInd xs (Some exp) intOpt fieldList exp.Type
                mkCallBoolRet fn [dexp]
            | BinaryPred(fn, intOptPair, fieldListPair) ->
                let (intOpt1, intOpt2) = intOptPair
                let (fieldList1, fieldList2) = fieldListPair
                let dexp1 = mkDerefExpInd xs (Some exp) intOpt1 fieldList1 exp.Type
                let dexp2 = mkDerefExpInd xs (Some exp) intOpt2 fieldList2 exp.Type
                mkCallBoolRet fn [dexp1; dexp2]

        // ----------------------------------------------------------------------------
        // misc functions
        let matchAndExpand xs xss =
           List.zip xs xss |> List.collect (fun (x, xs') -> [for x' in xs' -> (x, x')])

        let specAndRest d =
            match d with 
            | Top.FunctionDecl h -> 
               h.Name.StartsWith("\\") || h.Name.StartsWith("_")
            | _ -> true
        let collectDryadFunctions decls =
            for d in decls do
                match d with 
                | Top.FunctionDecl h ->
                    if ((funHasAnyDryadAttr h) || (funHasAnyBoogieAttr h)) then 
                        dryadFunDict.[h.Name] <- h
                | Top.Global (gr, _) ->
                    dryadGlobVarDict.[gr.Name] <- gr
                | _ -> ()

            decls
                        
        let analyzeFunctions decls =
            let globReachCall = Expr.Call( { bogusEC with Type = Type.OSet }, dryadFunDict.["glob_reach"], [], [])

            let mkSetDiffStmt  (e1 : Expr) (e2 : Expr) = Expr.Call(e1.Common, dryadFunDict.["\oset_diff"], [], [e1; e2])
            let mkSetUnionStmt (e1 : Expr) (e2 : Expr) = Expr.Call(e1.Common, dryadFunDict.["\oset_union"], [], [e1; e2])
            let mkEmptySet = Expr.Call ({ bogusEC with Type = Type.OSet }, dryadFunDict.["\oset_empty"], [], [])
            let mkUniverseSet = Expr.Call ({ bogusEC with Type = Type.OSet }, dryadFunDict.["\oset_universe"], [], [])
            let mkSetDisjStmt  (e1 : Expr) (e2 : Expr) = Expr.Call(boolBogusEC(), dryadFunDict.["\oset_disjoint"], [], [e1; e2])
            let mkSetInStmt  (e1 : Expr) (e2 : Expr) = Expr.Call(boolBogusEC(), dryadFunDict.["\oset_in"], [], [e1; e2])
            let mkSetSingleton (e1 : Expr)             = Expr.Call(e1.Common, dryadFunDict.["\oset_singleton"], [], [e1])

            let rec createReachSetUnion dryadMap (efs : (Expr * Function) list) =
                match efs with
                | [] -> mkEmptySet 
                | [(e, f)] -> mkReachCallExp dryadMap f e
                | (e, f) :: tail -> 
                    let recCall = createReachSetUnion dryadMap tail
                    mkSetUnionStmt (mkReachCallExp dryadMap f e) recCall 

            let mkUnionFromList (xs : Expr list) = 
                if xs.IsEmpty then mkEmptySet
                elif xs.Length = 1 then xs.Head
                else (xs.Tail |> List.fold (fun acc x -> mkSetUnionStmt acc x) xs.Head)

            let mkReachCallExpList (dryadMap: Map<string, DryadType>) (pred : Function) (xs : Expr list) = 
                let typeDecl = getTypeDeclExp xs.Head
                let reachFun = getReachFunOpt dryadMap pred typeDecl
                if reachFun.IsSome then mkReachCall reachFun.Value xs
                else mkEmptySet 
                
            let mkReachCallVar (dryadMap: Map<string, DryadType>) (pred : Function) (loc : Variable) = 
                let typeDecl = getTypeDecl loc
                let reachFun = getReachFunOpt dryadMap pred typeDecl
                if reachFun.IsSome then mkReachCall reachFun.Value [(mkRef loc)] //Expr.Call( { bogusEC with Type = Type.PtrSet }, reachFun.Value, [], [mkRef loc])
                else mkEmptySet

             // mkReachSetFromPred : Map<string, DryadType> -> Variable list -> Expr option -> ParamRetPred ->  Expr
            // creates reach set call from the parametrized predicate
            let mkReachSetFromPred dryadMap xs (expOpt : Expr option) pred = 
                match pred with 
                | UnaryPred (fn, intOpt, fieldList) -> 
                    let exp =  mkDerefExpInd xs expOpt intOpt fieldList fn.Parameters.Head.Type
                    mkReachCallExpList dryadMap fn [exp]
                | BinaryPred(fn, intOptPair, fieldListPair) -> 
                    let (intOpt1, intOpt2) = intOptPair
                    let (fieldList1, fieldList2) = fieldListPair
                    let exp1 = mkDerefExpInd xs expOpt intOpt1 fieldList1 fn.Parameters.Head.Type
                    let exp2 = mkDerefExpInd xs expOpt intOpt2 fieldList2 fn.Parameters.Tail.Head.Type
                    mkReachCallExpList dryadMap fn [exp1; exp2]


            let name2Fn = new Dict<_,_>()
            for d in decls do
                match d  with
                | Top.FunctionDecl h -> 
                    let specToStr isSpec =
                        match isSpec with
                        | true -> "Spec"
                        | false -> "Regular"
                    name2Fn.[h.Name] <- h
                | _ -> ()

            let FieldMaps = new Dict<string, Map<Variable, Expr>>()
            let DerefLocs = new HashSet<Variable>()
            let addToDerefLocs note loc =
                if DerefLocs.Add(loc) = true then printfn "  [%s] loc(%s) added to the deref locs" note loc.Name

            let analyzeCond e =
                let rec collectDeref el dfl =
                    match el with
                    | [] -> dfl
                    | exp :: rest ->
                        match exp with
                        | Cast( _,_, Ref (_, loc)) when loc.Type.IsPtr -> 
                            dfl @ [loc]
                        | Deref(_, Dot(_, Ref(_, loc), _)) -> dfl @ [loc]
                        | Prim(_, _, nel) -> 
                            let ndfl = collectDeref nel []
                            collectDeref rest dfl @ ndfl
                        | _ -> 
                            collectDeref rest dfl
                match e with 
                | Prim(_, _, el) -> 
                    let dfl = collectDeref el []
                    dfl |> List.iter (fun x -> (addToDerefLocs "if cond" x))
                | _ -> () 

            let getUnfoldStmt() =
                let mutable unfoldStmt = []
                let unfoldName = "_dryad_unfoldAll"
                let (isThere, unfoldAllFunc) = dryadFunDict.TryGetValue(unfoldName)
                if (isThere) then
                    for loc in DerefLocs do 
                        let unfoldAllExpr = Expr.Call(boolBogusEC(), unfoldAllFunc, [], [Expr.Cast({bogusEC with Type = ObjectT}, CheckedStatus.Checked, mkRef loc)])
                        unfoldStmt <- unfoldStmt @ [Expr.MkAssume(unfoldAllExpr)]
                    unfoldStmt
                else [notInDictFail unfoldName]
            
            let blockLevel = ref 0
            let stmtCnt = ref 0
            //let ghostStateVar = Variable.CreateUnique ("_dryad_S" + ((!blockLevel).ToString()) + "#"+ ((!stmtCnt).ToString())) Type.MathState VarKind.SpecLocal
            let mkGhostStateVar (bn : int) (sn : int) = Variable.CreateUnique ("_dryad_S" + (bn.ToString()) + "#" + (sn.ToString())) Type.MathState VarKind.SpecLocal
            let dummyVar = Variable.CreateUnique "##dummy##" Type.Bogus VarKind.Local
            let lastUpdatedLoc = ref (dummyVar)
            let curStateVar = ref (dummyVar)
            let nowState = Expr.Macro ({ bogusEC with Type = Type.MathState }, "_vcc_current_state", [])
            let getVarPairs pr = 
                match pr with
                | (Ref(_, vpr1), Ref(_, vpr2)) -> (vpr1, vpr2)
                | (pr1, pr2) -> failwith("[top]expected a pair of Refs " + pr2.ToStringWT(true))

// ----------------------------------------------------------------------------------------------------------------------------------
            let rec printVarDecl stmt =
                match stmt with
                | VarDecl(_, v, _) -> printfn "var: %s" (v.ToString())
                | Block(_, es, _) -> List.iter printVarDecl es
                | If(_, _, _, te, ee) -> 
                    printVarDecl te
                    printVarDecl ee
                | Macro(_, "while", [_; _; lb]) -> printVarDecl lb
                | _ as us -> () //printfn "Unprocessed expr: %s" (us.ToString())

            let rec mapRecEnv env f stmts =
                match stmts with
                | [] -> []
                | stmt :: stmts' ->
                    let (xstmt, env') = f(stmt, env)
                    xstmt @ (mapRecEnv env' f stmts')

            let rec mapEnv locs dlocs ltups cnt f stmts =
                match stmts with
                | [] -> []
                | stmt :: stmts' -> 
                    let (xstmt, locs', dlocs', ltups', cnt') = f(stmt, locs, dlocs, ltups, cnt)
                    xstmt :: (mapEnv locs' dlocs' ltups' cnt' f stmts')

            let findAssignType lhs rhs =
                match lhs with
                | Ref(_, varLhs) ->
                    match rhs with 
                    | Prim(_) | IntLiteral(_) | Macro(_, "const", _) -> AssignType.Simple(varLhs, None)
                    | Ref(_, varRhs) -> AssignType.Simple(varLhs, Some(varRhs))
                    | Deref(_, Dot(_, Ref(_, varRhs), fld)) -> AssignType.FieldLoad(varLhs, varRhs, fld)
                    | Call(_) as cs -> AssignType.FunCall(varLhs, cs)
                    | _ -> failwith ("[ref] unrecognized rhs " + (rhs.ToString()) + " in " + (lhs.ToString()) + " := " + (rhs.ToString()))
                | Deref(_, Dot(_, Ref(_, varLhs), fld)) -> 
                    match rhs with 
                    | IntLiteral(_) | Macro(_, "const", _) -> AssignType.FieldStore(varLhs, fld, None)
                    | Ref(_, varRhs) -> AssignType.FieldStore(varLhs, fld, Some(varRhs))
                    | _ -> failwith ("unrecognized rhs " + (rhs.ToString()) + " in " + (lhs.ToString()) + " := " + (rhs.ToString()))
                | _ -> failwith ("[top] unrecognized lhs " + (lhs.ToString()) + " in " + (lhs.ToString()) + " := " + (rhs.ToString()))

            // ########################################################################################################################################################################################
            // dryad primitives
            let mkCurVarState id = // _(ghost \state S<id> = \now())
                let ghostStateVar = Variable.CreateUnique ("_dryad_S" + (id.ToString())) Type.MathState VarKind.SpecLocal
                (ghostStateVar, [VarDecl(bogusEC, ghostStateVar, []); Expr.SpecCode(Macro(bogusEC, "=", [mkRef ghostStateVar; nowState]))])

            // v id -> (Var, ExprList)
            // create ghost var of typ
            let mkSSAVar (v : Variable) id =
                let ghostSSAVar = Variable.CreateUnique (v.Name + (id.ToString())) v.Type VarKind.SpecLocal
                (ghostSSAVar, [VarDecl(bogusEC, ghostSSAVar, []); Expr.SpecCode(Macro(bogusEC, "=", [mkRef ghostSSAVar; (mkRef v)]))])
           
            // unfold
            let mkUnfoldUnDef dryadMap x def =
                let dryadType = getDryadType dryadMap (getTypeDeclExp x)
                let unfoldFunOpt = dryadType.unfoldDefs.TryFind(def)
                if unfoldFunOpt.IsSome then 
                    let unfoldFun = unfoldFunOpt.Value
                    assert isUnaryDryadPred unfoldFun
                    let unfoldExpr = mkCallBoolRet unfoldFun [x] 
                    Expr.MkAssume(unfoldExpr)
                else notInMapFail def "unfoldDefs"
            let mkUnfoldUnDefLoc dryadMap loc def = mkUnfoldUnDef dryadMap (mkRef loc) def

            let mkUnfoldBinDef dryadMap hd tl def =
                let typeDecl = getTypeDeclExp hd
                assert (typeDecl = getTypeDeclExp tl)
                let dryadType = getDryadType dryadMap typeDecl
                let unfoldFunOpt = dryadType.unfoldDefs.TryFind(def)
                if unfoldFunOpt.IsSome then
                    let unfoldFun = unfoldFunOpt.Value
                    assert isBinaryDryadPred unfoldFun
                    let unfoldExpr = mkCallBoolRet unfoldFun [hd; tl]
                    Expr.MkAssume(unfoldExpr)
                else notInMapFail def "unfoldDefs"

            // Function list (Function -> Bool) Expr list -> Expr list
            // Given a list function a criterion for a function and parameters, produce assume function calls for functions satisfying the criterion
            let funs2Assumes funs filterFun xs = 
                funs |> List.filter filterFun
                     |> List.map (fun fn -> mkCallBoolRet fn xs)
                     |> List.map Expr.MkAssume

            let defs2Unfolds defNames dryadType filterFun xs = 
                let funs = defNames |> List.map (fun x -> dryadType.unfoldDefs.[x]) // well-formed dryadType.unfold must assure that each df in defNames exists
                funs2Assumes funs filterFun xs
            
            // DryadType (Function -> bool) Expr list -> Expr list
            // produce all assume unfold func calls, where func satisfy the criterion given in filterFun
            let allDryadTypeUnfolds dryadType filterFun xs =
                let funs = Map.toList dryadType.unfoldDefs |> List.map (fun (_, f)  -> f)
                funs2Assumes funs filterFun xs

            let mkUnfoldAllUnDefs dryadMap x =
                let dryadType = getDryadType dryadMap (getTypeDeclExp x)
                allDryadTypeUnfolds dryadType isUnaryDryadPred [x]
                (*let defNames = dryadType.defNames
                defs2Unfolds defNames dryadType isUnaryDryadPred [x]*)

            let mkUnfoldAllUnDefLoc dryadMap loc = mkUnfoldAllUnDefs dryadMap (mkRef loc)

            let mkUnfoldAllBinDefs dryadMap hd tl =
                let typeDecl = getTypeDeclExp hd
                assert (typeDecl = getTypeDeclExp tl)
                let dryadType = getDryadType dryadMap typeDecl
                allDryadTypeUnfolds dryadType isBinaryDryadPred [hd; tl]
                (*let defNames = dryadType.defNames
                defs2Unfolds defNames dryadType isBinaryDryadPred [hd; tl] *)

            // TODO: is there a binary dryad predicate version of this function?
            let mkUnfoldDefsFld dryadMap loc (fld : Field) =
                //printfn "loc %s ; fld %s" ((loc:Variable).Name) (fld.Name)
                let typeDecl = getTypeDecl loc
                let fldExists = typeDecl.Fields |> List.exists (fun x -> x = fld)
                //if fldExists then printfn "fld %s exists in typeDecl" (fld.Name) else printfn "fld %s does NOT exist in typeDecl!" (fld.Name)
                let dryadType = getDryadType dryadMap typeDecl
                if fldExists then
                    let fieldInf = dryadType.fieldInf.[fld.Name]                
                    defs2Unfolds fieldInf dryadType isUnaryDryadPred [(mkRef loc)]    
                else
                    mkUnfoldAllUnDefLoc dryadMap loc
                //if not fieldInf.IsEmpty && (fieldInf |> List.forall (fun x -> dryadType.defNames |> List.exists(fun y -> x = y))) then [mkUnfoldUnDef dryadMap loc "all-un"]
                //else 
                //fieldInf |> List.map (fun x -> mkUnfoldUnDefLoc dryadMap loc x)

           // -------------------------------------------------------------------------------------------------------------------------       

            // unconditionally maintaining the predicates and the functions
            // ---------------------------------------------------------------------------------------------------------------------------
            let mkCallPrePost fn xs pre post =
                Expr.Call(boolBogusEC(), fn, [], xs @ [(mkRef pre); (mkRef post)])

            let mkSameUnDef dryadMap exp def preState postState =
                let typeDecl = getTypeDeclExp exp
                let dryadType = getDryadType dryadMap typeDecl
                let sameDef = dryadType.sameDefs.TryFind(def)
                if sameDef.IsSome then
                    let sameDefFun = sameDef.Value
                    assert isUnaryDryadPred sameDefFun
                    let sameDefsExpr = mkCallPrePost sameDefFun [exp] preState postState
                    Expr.MkAssume(sameDefsExpr)
                else notInMapFail def "sameDefs" 
            let mkSameUnDefLoc dryadMap loc def preState postState = 
                mkSameUnDef dryadMap (mkRef loc) def preState postState
            
            let defs2Sames defNames allDefNames dryadType filterFun xs preState postState =            
                let funs = Set.difference (Set.ofList allDefNames) (Set.ofList defNames )                    
                                |> Set.toList
                                |> List.map (fun x -> dryadType.sameDefs.[x])
                funs2Assumes funs filterFun (xs @ [(mkRef preState); (mkRef postState)])                   

            let mkSameUnDefsFld dryadMap loc (fld : Field) preState postState = 
                let typeDecl = getTypeDecl loc 
                let dryadType = getDryadType dryadMap typeDecl

                let fieldInf = dryadType.fieldInf.[fld.Name]
                defs2Sames fieldInf dryadType.defNames dryadType isUnaryDryadPred [(mkRef loc)] preState postState

            let mkSameBinDefsFld dryadMap hd tl (fld: Field) preState postState = 
                let typeDecl = getTypeDeclExp hd
                let dryadType = getDryadType dryadMap typeDecl
                let fieldInf = dryadType.fieldInf.[fld.Name]
                defs2Sames fieldInf dryadType.defNames dryadType isBinaryDryadPred [hd; tl] preState postState
            // -----------------------------------------------------------------------------------------------------------------------------

            // conditionally maintaining the predicates and the functions
            // ------------------------------------------------------------------------------------------------------------------------------
            let mkCondSameUnDef dryadMap cloc loc def preState postState = 
                let typeDecl = getTypeDecl loc
                let dryadType = getDryadType dryadMap typeDecl
                let condSameDef = dryadType.condDefs.TryFind(def)
                if condSameDef.IsSome then
                    let condSameDefFun = condSameDef.Value
                    assert isCondUnaryDryadPred condSameDefFun
                    let condSameDefsExpr = mkCallPrePost condSameDefFun [(mkRef cloc); (mkRef loc)] preState postState 
                    Expr.MkAssume(condSameDefsExpr)
                else notInMapFail def "condSameDefs"

            let mkCondSameUnDefs dryadMap loc xs def preState postState =
                xs |> List.filter (fun x -> x <> loc) |> List.map (fun x -> mkCondSameUnDef dryadMap loc x def preState postState)
                
            let defs2CondSames defNames dryadType filterFun cexp xs preState postState =
                let funs = defNames |> List.map (fun x -> dryadType.condDefs.[x])
                let filterFun' x = (filterFun x) && (isFunFirstParamType (cexp: Expr).Type) x
                funs2Assumes funs filterFun' ((cexp :: xs) @ [(mkRef preState); (mkRef postState)])
                (*       |> List.filter filterFun
                         |> List.filter (isFunFirstParamType (cexp: Expr).Type)
                         |> List.map (fun fn -> mkCallPrePost fn (cexp :: xs) preState postState)
                         |> List.map Expr.MkAssume *)

            let mkCondSameUnDefsFld dryadMap cloc loc (fld: Field) preState postState =
                let typeDecl = getTypeDecl loc
                //assert (typeDecl = getTypeDecl cloc)
                let dryadType = getDryadType dryadMap typeDecl
                let fieldInf = dryadType.fieldInf.[fld.Name]
                defs2CondSames fieldInf dryadType isCondUnaryDryadPred (mkRef cloc) [(mkRef loc)]  preState postState

            let mkCondSameUnDefsAll dryadMap cexp locexp preState postState =
                let typeDecl = getTypeDeclExp cexp         
                let dryadType = getDryadType dryadMap typeDecl
                let funs = (Map.toList dryadType.condDefs)  |> (List.map (fun (s, f) -> f))
                
                let args' = [cexp ; locexp ; (mkRef preState) ; (mkRef postState)]       
                let ptrArgs' = args' |> List.filter (fun x -> x.Type.IsPtr)         
                let filterFun' x = (isCondUnaryDryadPred x) &&  (canMatchFunPtrParams x ptrArgs') 
                funs2Assumes funs filterFun' args'

            let mkCondSameBinDefsFld dryadMap cexp hd tl (fld: Field) preState postState =
                let typeDecl = getTypeDeclExp hd
                assert (typeDecl = getTypeDeclExp tl)
                let dryadType = getDryadType dryadMap typeDecl
                let fieldInf = dryadType.fieldInf.[fld.Name]
                defs2CondSames fieldInf dryadType isCondBinaryDryadPred cexp [hd; tl] preState postState

            let mkCondSameBinDefsAll dryadMap cexp hd tl preState postState =
                let typeDecl = getTypeDeclExp cexp
                let dryadType = getDryadType dryadMap typeDecl

                let funs = (Map.toList dryadType.condDefs)  |> (List.map (fun (s, f) -> f))                
                let args' = [cexp ; hd; tl ; (mkRef preState) ; (mkRef postState)]       
                let ptrArgs' = args' |> List.filter (fun x -> x.Type.IsPtr)         
                let filterFun' x = (isCondBinaryDryadPred x) &&  (canMatchFunPtrParams x ptrArgs') //(isFunFirstParamType (getCexpType cexp) x)
                funs2Assumes funs filterFun' args'
            // ----------------------------------------------------------------------------------------------------------------------------------------------

            // maintaining disjoint
            // ------------------------------------------------------------------------------------------------------------------------------
            let mkDisjSameUnDef dryadMap heapletPre loc def preState postState = 
                let typeDecl = getTypeDecl loc
                let dryadType = getDryadType dryadMap typeDecl
                let disjSameDef = dryadType.disjDefs.TryFind(def)
                if disjSameDef.IsSome then
                    let disjSameDefFun = disjSameDef.Value
                    assert isUnaryDryadPred disjSameDefFun
                    let disjSameDefsExpr = mkCallPrePost disjSameDefFun [heapletPre; (mkRef loc)] preState postState 
                    Expr.MkAssume(disjSameDefsExpr)
                else notInMapFail def "disjSameDefs"

            let mkDisjSameUnDefs dryadMap loc heapletPre xs def preState postState =
                xs |> List.filter (fun x -> x <> loc) |> List.map (fun x -> mkDisjSameUnDef dryadMap heapletPre x def preState postState)
                
            let defs2DisjSames defNames dryadType filterFun heapletPre xs preState postState =
                let funs = defNames |> List.map (fun x -> dryadType.disjDefs.[x])
                let filterFun' x = (filterFun x) && (isFunFirstParamType (heapletPre: Expr).Type) x
                funs2Assumes funs filterFun' ((heapletPre :: xs) @ [(mkRef preState); (mkRef postState)])

            let mkDisjSameUnDefsFld dryadMap heapletPre loc (fld: Field) preState postState =
                let typeDecl = getTypeDecl loc
                let dryadType = getDryadType dryadMap typeDecl
                let fieldInf = dryadType.fieldInf.[fld.Name]
                defs2DisjSames fieldInf dryadType isUnaryDryadPred heapletPre [(mkRef loc)]  preState postState

            let mkDisjSameUnDefsAll dryadMap heapletPre locexp preState postState =
                let typeDecl = getTypeDeclExp locexp         
                let dryadType = getDryadType dryadMap typeDecl
                let funs = (Map.toList dryadType.disjDefs)  |> (List.map (fun (s, f) -> f))
                
                let args' = [heapletPre ; locexp ; (mkRef preState) ; (mkRef postState)]       
                let ptrArgs' = args' |> List.filter (fun x -> x.Type.IsPtr)         
                let filterFun' x = (isUnaryDryadPred x) &&  (canMatchFunPtrParams x ptrArgs')
                funs2Assumes funs filterFun' args'

            let mkDisjSameBinDefsFld dryadMap heapletPre hd tl (fld: Field) preState postState =
                let typeDecl = getTypeDeclExp hd
                assert (typeDecl = getTypeDeclExp tl)
                let dryadType = getDryadType dryadMap typeDecl
                let fieldInf = dryadType.fieldInf.[fld.Name]
                defs2DisjSames fieldInf dryadType isBinaryDryadPred heapletPre [hd; tl] preState postState

            let mkDisjSameBinDefsAll dryadMap heapletPre hd tl preState postState =
                let typeDecl = getTypeDeclExp hd
                let dryadType = getDryadType dryadMap typeDecl

                let funs = (Map.toList dryadType.disjDefs)  |> (List.map (fun (s, f) -> f))                
                let args' = [heapletPre ; hd; tl ; (mkRef preState) ; (mkRef postState)]       
                let ptrArgs' = args' |> List.filter (fun x -> x.Type.IsPtr)         
                let filterFun' x = (isBinaryDryadPred x) &&  (canMatchFunPtrParams x ptrArgs') //(isFunFirstParamType (getCexpType cexp) x)
                funs2Assumes funs filterFun' args'
                //let allDefNames = dryadType.defNames
                //defs2DisjSames allDefNames dryadType isBinaryDryadPred cexp [hd; tl] preState postState
            // ----------------------------------------------------------------------------------------------------------------------------------------------
            
            let sameFields dryadMap loc preState =
                let typeDecl = getTypeDecl loc
                let dryadType = getDryadType dryadMap typeDecl
                let typeFields = typeDecl.Fields
                typeFields |> List.map (fun fld -> 
                                let derefExpr = (mkDerefExpr loc fld)
                                mkEq (derefExpr) (mkOldStmt (mkRef preState) derefExpr))

            let neqSameFields dryadMap expx locy preState =
                (sameFields dryadMap locy preState) |> List.map (fun exp -> Expr.MkAssume(mkImpl (mkNot(mkEq expx (mkRef locy))) exp))

            let notInHeapletSameFields dryadMap heaplet loc preState =
                let notInHeaplet = mkNot (mkSetInStmt (mkRef loc) (mkOldStmt (mkRef preState) heaplet))
                (sameFields dryadMap loc preState) |> List.map (fun exp -> Expr.MkAssume(mkImpl notInHeaplet exp))                

            let defs2BaseCalls defNames dryadType filterFun xs =
                defNames |> List.map (fun x-> dryadType.baseDefs.[x])
                         |> List.filter filterFun
                         |> List.map (fun fn -> mkCallBoolRet fn xs)
                        
            let mkBinBaseAsserts dryadMap hd tl =
                let typeDecl = getTypeDeclExp hd
                assert (typeDecl = getTypeDeclExp tl)
                let dryadType = getDryadType dryadMap typeDecl
                let allDefNames = dryadType.defNames
                defs2BaseCalls allDefNames dryadType isBinaryDryadPred [hd; tl]
                    |> List.map Expr.MkAssert                                
             
            let instLemma dryadMap def (args: Expr list) =
                assert(not args.IsEmpty)    
                let typeDecl = getTypeDeclExp args.Head
                let dryadType = getDryadType dryadMap typeDecl
                let lemmaFun = dryadType.lemmaDefs.[def]
                Expr.SpecCode(mkCallVoidRet lemmaFun args)

            // dryadMap args -> Expr list
            // instantiate lemmas with matching signature (the same number of args and matching arg types)
            let instLemmas dryadMap (args:Expr list) =
                let typeDecl = getTypeDeclExp args.Head
                let dryadType = getDryadType dryadMap typeDecl
                let lemmasFun = Map.toList dryadType.lemmaDefs 
                                    |> List.map (fun (s, f) -> f)
                                    |> List.filter (fun f -> (canMatchParams f.Parameters args))
                lemmasFun |> List.map (fun f -> Expr.SpecCode(mkCallVoidRet f args))

            // all dryad defs of fields' dereferences of _bl_, besides _flds_, that do not depend on x, must remain the same with pre and post state          
            let mkOtherFldsDefsSame dryadMap bl flds preState postState =
                let typeDecl = getTypeDecl bl
                let dryadType = getDryadType dryadMap typeDecl
                let fields' = typeDecl.Fields |> List.filter (fun f -> (not (List.exists(fun f' -> f = f') flds)))                              
                //typeDecl.Fields 
                //|> List.filter (fun f -> f <> fld && f.Type.IsPtr)
                fields' |> List.map (mkDerefExpr bl)
                        |> List.map (fun x -> mkCondSameUnDefsAll dryadMap (mkRef bl) x preState postState)
                        |> List.collect id

            let rec collectCalls x f =
                let aux x' acc =
                    match x with                
                    | Call(_, fn, _, _) as cexp -> if (f fn) then acc @ [cexp] else acc
                    | Macro(_, "lbl_split", exp) 
                    | Macro(_, "ite", exp) -> 
                        List.fold (fun ac el -> ac @ (collectCalls el f)) acc exp
                    | Prim(_, _, xs) ->                            
                        List.fold (fun ac el -> ac @ (collectCalls el f)) acc xs
                    | _ -> acc
                aux x []
            
            let getNaryDryadPreds xs n = 
                xs |> List.fold (fun acc el -> acc @ (collectCalls el (isNaryDryadPred n))) []
            let getUnaryDryadPreds  xs = getNaryDryadPreds xs 1
            let getBinaryDryadPreds xs = getNaryDryadPreds xs 2

            let getDryadPreds formals xs =
                (getUnaryDryadPreds xs) @ (getBinaryDryadPreds xs) 
                    |> List.map (mkParamRetPred formals)
            let dryadPredsReachReq dryadMap formals actuals xs = 
                getDryadPreds formals xs 
                    |> List.map (mkReachSetFromPred dryadMap actuals None)
            let dryadPredsReachRet dryadMap formals actuals retOpt xs =
                getDryadPreds formals xs
                    //|> List.filter isRetPred
                    |> List.map (mkReachSetFromPred dryadMap actuals retOpt)
           
           
            let getArgsFromCall x =
                match x with
                | Call(_, fn, _, args) -> args
                | _ -> failwith "Expected Call expression" 
            let getFunFromCall x = 
                match x with 
                | Call(_, fn, _, args) -> fn
                | _ -> failwith "Expected Call expression"

            // Expr -> bool 
            // Precond: cexp must be Expr.Call
            // Returns true if all arguments are Expr.Ref
            let allCallArgsAreRefs cexp =
                match cexp with
                | Call(_, _, _, args) -> args |> List.forall isExprRef
                | _ -> failwith "[allCallArgsAreRefs]"

            // Expr list -> (Expr * Expr) list
            // transform expression representing binary dryad functions into its argument tuple
            let getDryadFunBinArgs xs =                    
                xs |> getBinaryDryadPreds 
                   |> List.map getCallFunArgs
                   |> List.map list2Tuple
            
            let getDryadFunUnArgs xs =
                xs |> getUnaryDryadPreds
                   |> List.map getCallFunArgs
                   
                    

            // Expr (Call) -> (Variable * Expr) list ->  Expr (Call)
            // In the function call replace 
            let replaceFormalsForActuals (x: Expr) fa =
                let replaceFormalForActual (cexp : Expr) var exp =
                    let aux _ (e: Expr) =
                        if (isRefExprVar var e) then Some(exp)
                        else None
                    cexp.SelfMap(aux)
                List.fold (fun acc (f,a) -> replaceFormalForActual acc f a) x fa

            // Expr[Call] -> Expr list
            // transfrom the call expression into its postcondition's with formals replaced for actuals
            let getPostDryadCalls x =
                let fn      = getFunFromCall x
                let formals = fn.Parameters
                let actuals = getArgsFromCall x              
                let fa = List.zip formals actuals
                let dryadFuns = getUnaryDryadPreds fn.Ensures @ getBinaryDryadPreds fn.Ensures
                dryadFuns |> List.map (fun x -> replaceFormalsForActuals x fa)

           
            // env -> varLhs -> fld -> varRhs -> Expr list [lsegs]
            // infer lsegs based on lhs fld rhs and current env
            // requires: lhs and rhs are pointers
            
            let inferLsegs env (lhs : Expr) (fld : Field) (rhs : Expr) = 
                assert (lhs.Type.IsPtr && rhs.Type.IsPtr)
                let typeDecl = getTypeDeclExp lhs
                let dryadType = getDryadType env.tenv typeDecl
                //let ltups = env.ltups |> List.filter (fun (hd, tl) -> tl.Equals(lhs))
                let fieldInfs = dryadType.fieldInf.[fld.Name]
                defs2Unfolds fieldInfs dryadType isBinaryDryadPred [lhs; rhs] //*)
                

            // ****************************************************************************************************************************************************************************************
            // ******************************************************************  the main function of the dryad transformer *************************************************************************
            // ****************************************************************************************************************************************************************************************
            let rec dryadTrans(stmt, env) = 
                let newDenv loc = if List.exists(fun x -> x = loc) env.dlocs then env.dlocs else loc::env.dlocs
                // ====================================================================================================================================================================================
                let handleAssigns assignType =
                    match assignType with
                    | Simple(varLhs, varRhs) -> 
                        if (varLhs.Type.IsPtr) then
                            let unfoldLhs = if (varRhs.IsNone) then  (mkUnfoldAllUnDefLoc env.tenv varLhs) else []
                            let sillyAsserts = 
                                env.locs |> List.map (fun x-> mkBinBaseAsserts env.tenv (mkRef x) (mkRef x))
                                         |> List.collect id
                            
                            if (varRhs.IsSome) then 
                                assert varRhs.Value.Type.IsPtr
                                let varRhsVal = varRhs.Value
                                let relTuples = 
                                    let filterRelevantTuples (hd: Expr) (tl: Expr) =
                                        hd.HasSubexpr(isRefExprVar varRhsVal) || tl.HasSubexpr(isRefExprVar varRhsVal) 
                                    env.ltups |> List.filter (fun (hd, tl) -> filterRelevantTuples hd tl)
                                let newLhsTuples =                            
                                    let replaceVarRhs4VarLhs (e : Expr) = 
                                        let aux _ (x: Expr) =
                                            if x.HasSubexpr(isRefExprVar varRhsVal) then printfn "founds lhsVar";(Some (mkRef varLhs))
                                            else None
                                        e.SelfMap(aux)                                
                                    (relTuples |> List.map (fun (hd, tl) -> (replaceVarRhs4VarLhs hd, replaceVarRhs4VarLhs tl)))
                                let newTuples = env.ltups @ newLhsTuples
                                ([], sillyAsserts @ unfoldLhs, {env with ltups = newTuples})
                            else ([], sillyAsserts @ unfoldLhs, env)
                        else ([], [], env)
                    | FieldLoad(varLhs, varRhs, fld) ->
                        let dryadType = getDryadType env.tenv (getTypeDecl varRhs)
                        let unfoldRhs = mkUnfoldDefsFld env.tenv varRhs fld 
                        let derefExpr = mkDerefExpr varRhs fld                          

                        let relTuples = 
                            let filterRelevantTuples (hd: Expr) (tl: Expr) =
                                hd.HasSubexpr(isRefExprVar varLhs) || tl.HasSubexpr(isRefExprVar varLhs) 
                                || hd.HasSubexpr(isRefExprVar varRhs) || tl.HasSubexpr(isRefExprVar varRhs)                        
                            env.ltups |> List.filter (fun (hd, tl) -> filterRelevantTuples hd tl)

                        let newLhsTuples =                            
                            let replaceVarRhsFld4VarLhs (e : Expr) = 
                                let aux _ (x: Expr) =
                                    if x.HasSubexpr(isDotExpr varRhs fld) then (Some (mkRef varLhs))
                                    else None
                                e.SelfMap(aux)                                
                            (relTuples |> List.map (fun (hd, tl) -> (replaceVarRhsFld4VarLhs hd, replaceVarRhsFld4VarLhs tl)))

                        // for each (varRhs, tl) in the list of tuples if varRsh gets dereferenced through field fld add  (varRhs->fld, tl) to the list of tuples
                        let hdDerefTuples =
                            if (varLhs.Type.IsPtr) then
                                env.ltups |> List.filter (fun (hd, tl) -> hd.ExprEquals(mkRef varRhs) && (hd <> tl))
                                          |> List.map (fun (hd, tl) -> (mkRef varLhs, tl))
                            else []

                        let newTuples = env.ltups @ newLhsTuples @ hdDerefTuples

                        let unfoldLhs = if (varLhs.Type.IsPtr && tdHasAnyDryadAttr (getTypeDecl varLhs)) then mkUnfoldAllUnDefs env.tenv (mkRef varLhs)
                                        else []

                        let (locs', ghostExps) =
                            let (ghostSSAVar, ghostSSAExps) = mkSSAVar varRhs env.dcnt
                            (ghostSSAVar :: env.locs, ghostSSAExps)

                        if (varLhs = varRhs) then
                            let unfoldLsegs = relTuples |> List.map(fun (hd, tl) -> mkUnfoldAllBinDefs env.tenv hd tl)
                                                        |> List.collect id

                            let unfoldLsegNext = mkUnfoldAllBinDefs env.tenv (mkRef varLhs) (mkDerefExpr varRhs fld)//(Expr.MkDot(mkRef varRhs, fld))
                            (ghostExps @ unfoldRhs @ unfoldLsegNext, 
                             unfoldLhs @ unfoldRhs @ unfoldLsegs, 
                             {env with locs = locs'; ltups = newTuples; dcnt = env.dcnt + 1 })
                        else
                            // remove lhsTailTuples
                            let filterLhsTailTuples (tl: Expr) = tl.HasSubexpr(isRefExprVar varLhs) && (getTypeDeclExp tl = getTypeDecl varLhs)
                            let newTuples' = newTuples |> List.filter (fun (_, tl) -> not (filterLhsTailTuples tl))
                            (ghostExps @ unfoldRhs, 
                             unfoldLhs @ unfoldRhs, 
                             {env with locs = locs'; ltups = newTuples'; dcnt = env.dcnt + 1})                            

(* FIELD STORE *)   | FieldStore(varLhs, fld, optVarRhs) ->
                        let (preStateVar,  preStateStmt)  = mkCurVarState env.cnt
                        let (postStateVar, postStateStmt) = mkCurVarState (env.cnt + 1)
                        let VarDecl(_, postStateVar, _) = postStateStmt.Head  
                        let dryadType = getDryadType env.tenv (getTypeDecl varLhs)
                        let derefExpr = mkDerefExpr varLhs fld

                        let prevStateFieldAccess = 
                            mkOldStmt (mkRef preStateVar) derefExpr
                                                        
                        let isDryadLocRhs = optVarRhs.IsSome && optVarRhs.Value.Type.IsPtr && tdHasAnyDryadAttr (getTypeDecl optVarRhs.Value)
                        let relTuples = 
                            let filterRelevantTuples (hd: Expr) (tl: Expr) =
                                hd.HasSubexpr(isRefExprVar varLhs) || tl.HasSubexpr(isRefExprVar varLhs)
                                || (isDryadLocRhs && hd.HasSubexpr(isRefExprVar optVarRhs.Value))
                                || (isDryadLocRhs && tl.HasSubexpr(isRefExprVar optVarRhs.Value))                        
                            env.ltups |> List.filter (fun (hd, tl) -> (filterRelevantTuples hd tl))

                        let filterLhsHeadTuples (hd: Expr) = hd.HasSubexpr(isRefExprVar varLhs) && (getTypeDeclExp hd = getTypeDecl varLhs)
                        let lhsHeadTuples = 
                            env.ltups |> List.filter (fun (hd, _) -> filterLhsHeadTuples hd)
                        
                        let notLhsHeadTuples = 
                            env.ltups |> List.filter (fun (hd, _) -> not (filterLhsHeadTuples hd))
                          
                        // create tuple of tuples 
                        let conTuples = 
                            // filter a list of tuples whose head match the given tuple
                            let filterHeadTuples head = env.ltups |> List.filter (fun(hd, tl) -> hd.ExprEquals(head))
                            let singletonZip x ys = ys |> List.map (fun y -> (x, y))
                            env.ltups |> List.map (fun (hd, tl) -> singletonZip (hd, tl) (filterHeadTuples tl))
                                      |> List.collect id

                        let unfoldVars = (env.locs 
                                            |> List.filter (fun x -> x <> varLhs)
                                            |> List.map (fun x -> (mkUnfoldAllUnDefs env.tenv (mkRef x))) 
                                            |> List.collect id)
                                        @ (mkUnfoldDefsFld env.tenv varLhs fld)
                                        @ (if isDryadLocRhs then (mkUnfoldAllUnDefs env.tenv (mkRef optVarRhs.Value)) else [])

                        let unfoldLsegs =                             
                            let lsegTuples = (env.ltups |> List.filter (fun (hd, tl) ->  (not (hd.ExprEquals(tl))) && (not (tl.HasSubexpr(isRefExprVar varLhs)))))
                                             @ (env.ltups |> List.filter (fun (hd, tl) -> hd.ExprEquals(derefExpr)))                             
                            lsegTuples  |> List.map (fun (hd, tl) -> mkUnfoldAllBinDefs env.tenv hd tl)
                                        |> List.collect id

                        let inferredLsegUnfolds = if isDryadLocRhs then inferLsegs env (mkRef varLhs) fld (mkRef optVarRhs.Value)
                                                  else []    
                        
                        let sameUnDefs = if isDryadLocRhs then  mkSameUnDefsFld env.tenv varLhs fld preStateVar postStateVar
                                         else env.locs  |> List.filter (fun x -> x.Type = varLhs.Type)
                                                        |> List.map (fun x -> mkSameUnDefsFld env.tenv x fld preStateVar postStateVar)
                                                        |> List.collect id

                        let otherFldsSameUnDefs = mkOtherFldsDefsSame env.tenv varLhs [fld] preStateVar postStateVar

                        let condExpr = mkRef varLhs

                        let sameBinDefs =  
                            let tuples = lhsHeadTuples
                            tuples |> List.map (fun (hd, tl) -> mkSameBinDefsFld env.tenv hd tl fld preStateVar postStateVar)
                                   |> List.collect id
                        let condSameUnDefs  = env.locs  |> List.filter (fun x -> x <> varLhs)
                                                        |> List.map    (fun x -> mkCondSameUnDefsAll env.tenv condExpr (mkRef x) preStateVar postStateVar)
                                                        |> List.collect id 

                        // Expr -> Expr
                        // map Expr.Dot(varLhs, field) to \at(preState, Expr.Deref(Expr.Dot(varLhs, field))))
                        let replaceFieldStore (e : Expr) =
                            let aux _ (x : Expr) = 
                                if x.HasSubexpr(isDotExpr varLhs fld) then Some(prevStateFieldAccess)
                                else None
                            e.SelfMap(aux)

                        // Expr -> Expr 
                        // map Expr.Ref(varLhs) -> \at(preState, Expr.Deref(Expr.Dot(varLhs, field)))
                        let replaceWithPrevStateDerefField (e : Expr) =
                            if (isRefExprVar varLhs e) then prevStateFieldAccess
                            else e
                        
                        let condSameBinDefs = env.ltups |> List.map (fun (hd, tl) -> (replaceWithPrevStateDerefField hd, tl))
                                                        |> List.map (fun (hd, tl) -> (replaceFieldStore hd, replaceFieldStore tl))                                                                                                                                            
                                                        |> List.map (fun (hd, tl) -> mkCondSameBinDefsAll env.tenv condExpr hd tl preStateVar postStateVar)
                                                        |> List.collect id                                                                       
                        
                        let preserveFields = (env.locs 
                                              |> List.filter (fun x -> x <> varLhs)
                                              |> List.filter (fun x -> x.Type = varLhs.Type)
                                              |> List.map (fun x -> neqSameFields env.tenv (mkRef varLhs) x preStateVar))
                                              |> List.collect id

                        let postStmt = postStateStmt 
                                       @ otherFldsSameUnDefs
                                       @ sameUnDefs     @ sameBinDefs
                                       @ condSameUnDefs 
                                       @ condSameBinDefs                            
                                       @ preserveFields
                                       @ unfoldVars 
                                       @ unfoldLsegs 
                        (preStateStmt, postStmt, {env with dlocs = (newDenv varLhs); ltups = notLhsHeadTuples;cnt = env.cnt + 2; dcnt = env.dcnt + 1})
(* FUNCTION CALL *) | FunCall(varLhs, cexp) ->           
                        let (fn, args) = getCallFunAndArgs cexp
                        let ptrActuals = args |> List.filter(fun x -> x.Type.IsPtr) 
                        let ptrFormals = fn.Parameters |> List.filter(fun x -> x.Type.IsPtr)

                        let (preStateVar, preStateStmt) = mkCurVarState env.cnt
                        let (postStateVar, postStateStmt) = mkCurVarState (env.cnt + 1)

                        let unfoldLocs = (env.locs |> List.map(fun x -> mkUnfoldAllUnDefs env.tenv (mkRef x)))
                                         @ (env.ltups |> List.map (fun (hd, tl) -> mkUnfoldAllBinDefs env.tenv hd tl))
                                         |> List.collect id

                        let locsDiffLhs = env.locs |> List.filter (fun x -> x <> varLhs) 
                        let nonNullActuals = ptrActuals |> List.filter (fun x -> (not (isNullExpr x)))

                        let condSameArgs = nonNullActuals |> List.filter (fun x -> tdHasAnyDryadAttr(getTypeDeclExp x))
                                                          |> List.map (fun cx -> locsDiffLhs |> List.map (fun vx -> mkCondSameUnDefsAll env.tenv cx (mkRef vx) preStateVar postStateVar) 
                                                                                             |> List.collect id)
                                                          |> List.collect id  
                                                          
                        let locFlds = nonNullActuals |> List.map decompRefExpr
                                                     |> List.map (fun (v, optFld) -> if optFld.IsSome then (v, [optFld.Value]) else (v, []))
                        let otherSames  =  locFlds |> List.map (fun (v, flds) -> mkOtherFldsDefsSame env.tenv v flds preStateVar postStateVar)
                                                  |> List.collect id
                        let condSames = 
                           if varLhs.Type.IsPtr then 
                                    ((env.locs |> List.filter (fun x-> x <> varLhs) 
                                              |> List.map (fun x -> mkCondSameUnDefsAll env.tenv (mkRef varLhs) (mkRef x) preStateVar postStateVar))
                                    @ (env.ltups |> List.map (fun (hd, tl) -> mkCondSameBinDefsAll env.tenv (mkRef varLhs) hd tl preStateVar postStateVar)))
                                    |> List.collect id
                           else [] 
                                                    
                        if (varLhs.Type.IsPtr && not ptrActuals.IsEmpty) then
                            let argTuples = getDryadPreds ptrFormals fn.Ensures
                                              |> List.filter isBinaryParamRetPred
                                              |> List.map (mkExprArgsBin ptrActuals (mkRef varLhs))                                            
                            
                            let singletonRet = mkSetSingleton (mkRef varLhs)
                            let retPredsReach = (dryadPredsReachRet env.tenv ptrFormals ptrActuals (Some(mkRef varLhs)) fn.Ensures)
                                                
                            let paramTuples = 
                                if (env.curfn = fn.Name) then 
                                    let ptrFormalsExp = ptrFormals |> List.map mkRef
                                    getDryadPreds ptrFormals fn.Ensures
                                        |> List.filter isBinaryParamRetPred
                                        |> List.map (mkExprArgsBin ptrFormalsExp (mkRef varLhs))
                                else []

                            let ltups' = env.ltups @ argTuples @ paramTuples

                            let unfoldExtra = (argTuples @ paramTuples)
                                                |> List.map (fun (hd, tl) -> mkUnfoldAllBinDefs env.tenv hd tl)
                                                |> List.collect id

                            let argsReachSets = dryadPredsReachReq env.tenv ptrFormals ptrActuals fn.Requires                            
                            let globDiffArgs = if argsReachSets.IsEmpty then globSetPostRef
                                               else 
                                                let argsReachSetExp = argsReachSets |> mkUnionFromList
                                                mkSetDiffStmt globSetPostRef (mkOldStmt (mkRef preStateVar) argsReachSetExp)                            
                            
                            let heapletPre = argsReachSets |> mkUnionFromList    

                            let disjHeapletPre =
                                if argsReachSets.IsEmpty then []
                                else 
                                   locsDiffLhs |> List.map (fun vx -> mkDisjSameUnDefsAll env.tenv heapletPre (mkRef vx) preStateVar postStateVar)
                                               |> List.collect id 

                            let preserveFields =
                                if argsReachSets.IsEmpty then []
                                else 
                                    locsDiffLhs |> List.map (fun vx -> notInHeapletSameFields env.tenv heapletPre vx preStateVar)
                                                |> List.collect id

                            let assumeDisjStmts = retPredsReach |> List.map (fun x -> Expr.MkAssume(mkSetDisjStmt x globDiffArgs))
                            let updateGlobReachStmts = retPredsReach |> List.map (fun x -> Expr.SpecCode(Macro(bogusEC, "=", [globSetPostRef; (mkSetUnionStmt x globDiffArgs)])))

                            let assumeReachEq = Expr.MkAssume(mkEq globReachCall globSetPostRef)
                            let postStmt = postStateStmt @ assumeDisjStmts @ updateGlobReachStmts @ [assumeReachEq]
                            (preStateStmt, postStmt @ disjHeapletPre @ unfoldLocs @ unfoldExtra @ preserveFields, {env with ltups = ltups'; cnt = env.cnt + 2})
                        else
                            (preStateStmt, postStateStmt @ unfoldLocs @ condSameArgs @ otherSames @ condSames, {env with cnt = env.cnt + 2})
                // ====================================================================================================================================================================================

                match stmt with 
                | VarDecl(_, v, _) -> 
                    let vTypeDecl = if v.Type.IsPtr then Some (getTypeDecl v) else None
                    let dontAddToLocs = (List.exists (fun x -> x = v) env.locs || vTypeDecl.IsNone || not (tdHasAnyDryadAttr vTypeDecl.Value))
                    let locs' = if dontAddToLocs then env.locs else v::env.locs
                    ([stmt], { env with locs = locs'})
                | Call(_, {Name = "free"}, _, args) as cs ->
                    let arg = match args with [Cast(_, _, Ref(_, el))] -> el | _ -> failwith("unexepcted argument(s) to free")
                    let (preStateVar, preStateStmt) = mkCurVarState env.cnt
                    let (postStateVar, postStateStmt) = mkCurVarState (env.cnt + 1)

                    let condSameUnDefs = env.locs  |> List.filter (fun x -> x <> arg)
                                                   |> List.map    (fun x -> mkCondSameUnDefsAll env.tenv (mkRef arg) (mkRef x) preStateVar postStateVar)
                                                   |> List.collect id 

                    //mkCondSameUnDefs env.tenv arg env.locs "all-un" preStateVar postStateVar
                    //(env.locs |> List.filter (fun x -> x <> arg) |> List.map(fun x -> mkCondSameUnDef env.tenv x arg "all-un" preStateVar postStateVar))
                    let maintAcross = condSameUnDefs
                                      @ (env.ltups |> List.map (fun (hd, tl) -> mkCondSameBinDefsAll env.tenv (mkRef arg) hd tl preStateVar postStateVar)
                                                   |> List.collect id)

                    (preStateStmt @ cs :: postStateStmt @ maintAcross, { env with cnt = env.cnt + 2}) 
                | Call(_, fn, _, args) as cs ->
                    let (preStateVar, preStateStmt) = mkCurVarState env.cnt
                    let (postStateVar, postStateStmt) = mkCurVarState (env.cnt + 1)
                    let ptrActuals = args |> List.filter(fun x -> x.Type.IsPtr) 
                    if (not ptrActuals.IsEmpty) then
                        let unfoldLocs = (env.locs |> List.map(fun x -> mkUnfoldAllUnDefs env.tenv (mkRef x)))
                                         @ (env.ltups |> List.map (fun (hd, tl) -> mkUnfoldAllBinDefs env.tenv hd tl))
                                         |> List.collect id


                        (preStateStmt @ cs :: postStateStmt @ unfoldLocs (* @ assumeDisjStmts @ condSameArgs @ otherSames *), { env with cnt = env.cnt + 2})                                        
                    else
                        ([stmt], env)
                | Macro(_, "=", [lhs; rhs]) as assign -> 
                    let assignType = findAssignType (peelCast lhs) (peelCast rhs)
                    let (preStmt, postStmt, env') = handleAssigns assignType
                    if preStmt.IsEmpty && postStmt.IsEmpty then 
                        ([assign], { env with locs = env'.locs; dlocs = env'.dlocs; ltups = env'.ltups; cnt = env'.cnt; dcnt = env'.dcnt})
                    else 
                        (preStmt @ assign :: postStmt, {env with locs = env'.locs; dlocs = env'.dlocs; ltups = env'.ltups; cnt = env'.cnt; dcnt = env'.dcnt})
                | Macro(_, "spec", [Expr.Call(_, fn, _, _) as callExp]) as exp -> // FIXME: this should be removed
                    if fn.Name.Contains("lseg") then 
                        let lsegs = getDryadFunBinArgs [callExp]
                        ([stmt], {env with ltups = env.ltups @ lsegs})
                    else ([stmt], env)
                | Block(ec, es, bc) ->
                    let unfoldDerefs = env.dlocs |> List.map (fun x -> mkUnfoldAllUnDefLoc env.tenv x)
                    let unfoldLocs   = env.locs  |> List.map (fun x -> mkUnfoldAllUnDefLoc env.tenv x) |> List.collect id
                    let unfoldLsegs = env.ltups |> List.map (fun (hd, tl) -> mkUnfoldAllBinDefs env.tenv hd tl) |> List.collect id 
                    let stmts' = mapRecEnv env dryadTrans es
                    ([Block(ec, unfoldLocs @ unfoldLsegs @ stmts', bc)], env)
                | If(ec, tc, cond, te, ee) ->
                    let (te', thenEnv) = dryadTrans(te, env)
                    let (ee', elseEnv) = dryadTrans(ee, env)
                    let ltups' = thenEnv.ltups @ (List.filter (fun x -> not(List.exists (fun y -> x = y) thenEnv.ltups)) elseEnv.ltups)
                    ([If(ec, tc, cond, Block(ec, te', None), Block(ec, ee', None))], {env with ltups = ltups'})
                | Macro(ec, "while", [linv; lcond; lbody]) ->
                    let invList = match linv with Macro(_, "loop_contract", e) -> e | _ -> failwith("expected loop_contract macro")

                    let rec getInvs invs l =
                        match l with 
                        | [] -> invs
                        | Assert(_, e, el) :: rest -> getInvs (e::invs) rest
                        | _::rest -> 
                            getInvs invs rest
                    let invs = getInvs [] invList

                    let ltups = getDryadFunBinArgs invs
                    let ltups' = env.ltups @ ltups //(List.map (fun x -> getVarPairs x) lsegs) 

                    let (lbody', env') = dryadTrans(lbody, {env with ltups = ltups'})
                    let unfoldLocs   = env.locs  |> List.map (fun x -> mkUnfoldAllUnDefLoc env.tenv x) |> List.collect id
                    ([Macro(ec, "while", [linv; lcond; Block(ec, lbody', None)])] @ unfoldLocs, {env' with ltups = env'.ltups})
                | _ as s -> ([stmt], env)

            let rec printAssign stmt = 
                match stmt with
                | Macro(_, "=", [lhs; rhs]) -> 
                    (findAssignType (peelCast lhs) (peelCast rhs)) |> ignore
                | Block(_, es, _) -> List.iter printAssign es
                | If(_, _, _, te, ee) ->
                    printAssign te
                    printAssign ee
                | Macro(_, "while", [_; _; lb]) -> printAssign lb
                | _ -> ()
            

            // checkHeapletPre
            // purpose: given the list of requires clauses check the heaplet associated with precondition (specified as \assume(glob_reach == heaplet)
            let checkHeapletPre (fpre : Expr list) =                 
                let aux x =
                    let hasGlobReach (e : Expr) = 
                        match e with 
                        | Expr.Call(_, {Name = "glob_reach"}, _, []) -> true
                        | _ -> false
                    match x with 
                    | Expr.Call(_, {Name = "\\assume"}, _, [arg]) -> arg.HasSubexpr(hasGlobReach)
                    | _ -> false

                fpre |> List.exists (fun x -> aux x)

            // ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------                      
            let analyzeFuncBody fn dryadMap =
                let fp    = fn.Parameters
                let fb    = fn.Body
                let fpre  = fn.Requires
                let fpost = fn.Ensures
                match fb with
                | Some stmt -> 
                    match stmt with
                    | Block(ec, stmts, bc) -> 
                        let dryadCalls = (getUnaryDryadPreds fpre)
                                         |> List.map getPostDryadCalls 
                                         |> List.collect id
                        let ltups' = getDryadFunBinArgs (fpre @ dryadCalls)
                        let lsing' = getDryadFunUnArgs dryadCalls 
                                    |> List.collect id


                        let ptrParams = fp |> List.filter (fun x -> x.Type.IsPtr) 

                        let ptrParamsExp = ptrParams |> List.map(fun v -> mkRef v)
                        let reqPreds = getDryadPreds ptrParams fpre

                        reqPreds |> List.filter isBinaryParamRetPred
                                 |> List.iter printParamRetPred
                        let paramPredsReachSet = dryadPredsReachReq dryadMap ptrParams ptrParamsExp fpre 
                                                 |> mkUnionFromList

                        let retPreds = getDryadPreds ptrParams fpost

                        let xstmts = mapRecEnv {curfn = fn.Name; locs = []; dlocs = []; lsing = lsing'; ltups = ltups';
                                                tenv = dryadMap ; cnt = 0 ;dcnt = 0 } dryadTrans stmts

                        let paramsReachSet = paramPredsReachSet

                        let globSetPreDecl = Expr.VarDecl(bogusEC, globSetPre, [])
                        // FIXME
                        let initPreSetStmt = 
                            let x = if (checkHeapletPre fpre) 
                                    then globReachCall 
                                    else paramsReachSet
                            Expr.SpecCode(Macro(bogusEC, "=", [globSetPreRef; x]))
                        let globSetPostDecl = Expr.VarDecl(bogusEC, globSetPost, [])
                        let initPostSetStmt = Expr.SpecCode(Macro(bogusEC, "=", [globSetPostRef; globSetPreRef]))
                        let equivPostStmt = Expr.MkAssume(mkEq globReachCall globSetPostRef)
                        let dryadComment = Comment(bogusEC, " --- Dryad annotated function --- ")
                        Some(Block(ec, [dryadComment; globSetPreDecl; globSetPostDecl; initPreSetStmt; initPostSetStmt; equivPostStmt] @ xstmts, bc))
                    | _ -> 
                        printfn "Expected block of statements."
                        fb
                | None -> 
                    fb

            let analyzeFunction (f : Function) (env : DeclEnv) =                
                //if f.Body.IsSome then printfn " analyzing function %s " f.Name
                f.Body <- analyzeFuncBody f env.type2Dryad

                DerefLocs.Clear()

            // ======================== analyze decsl ==========================================
            let analyzeDryadTypeDecl (td : TypeDecl, env) = 
                let rec getDefNames xs = 
                    match xs with
                    | [] -> failwith "Custom attribute dryad expected"
                    | x :: xs' -> 
                        match x with 
                        | VccAttr(k, v) when k = "dryad" -> Array.toList(v.Split ':')
                        | _ -> getDefNames xs'
                   
                let dryadMap = env.type2Dryad
                let baseDryadType = 
                    if dryadMap.ContainsKey(td.Name) then failwith("analyzeDryadTypeDecl: unexpected existing type " + td.Name)
                    else defaultDryadType td
                let defNames' = getDefNames td.CustomAttr
                let newDryadMap = dryadMap.Add(td.Name, {baseDryadType with defNames = defNames' })
                { env with type2Dryad = newDryadMap  }
            
            let getParamLocType func = 
                let ptrParams = func.Parameters |> List.filter(fun x -> isTypeDecl(mkRef x))
                let typeDecl = if ptrParams.IsEmpty then failwith "Expected location type when adding to fun map." else getTypeDecl ptrParams.Head
                (ptrParams.Head, typeDecl)

            let addToFunMap (mapName, defName, func, env) =    
                let (hdVar, typeDecl) = getParamLocType func
                let dryadMap = env.type2Dryad
                let dryadType = getDryadType dryadMap typeDecl 
                let dryadMap' =
                    let updateMap dt = dryadMap.Add(typeDecl.Name, dt)
                    match mapName with
                    | "unfold" -> updateMap({ dryadType with unfoldDefs = dryadType.unfoldDefs.Add(defName, func) })
                    | "base"   -> updateMap({ dryadType with baseDefs   = dryadType.baseDefs.Add(defName, func) })
                    | "same"   -> updateMap({ dryadType with sameDefs   = dryadType.sameDefs.Add(defName, func) })
                    | "cond"   -> updateMap({ dryadType with condDefs   = dryadType.condDefs.Add(defName, func) })
                    | "disj"   -> updateMap({ dryadType with disjDefs   = dryadType.disjDefs.Add(defName, func) })
                    | "lemma"  -> updateMap({ dryadType with lemmaDefs  = dryadType.lemmaDefs.Add(defName, func) })
                    | _ -> failwith ("Unhandled map name " + mapName)
                { env with type2Dryad = dryadMap' }                
                          
            let analyzeDryadUnfoldFun (defName, func, env) =
                let env' = addToFunMap("unfold", defName, func, env)
                let dryadMap = env'.type2Dryad
                let containsDerefField fld v = 
                    let funcEnsures = (func : Function).Ensures
                    let res = funcEnsures |> List.exists(fun e -> e.HasSubexpr(isDotExpr v fld))
                    res
                let (hdVar, typeDecl) = getParamLocType func
                let depFields = typeDecl.Fields |> List.filter (fun fld -> containsDerefField fld hdVar)
                let dryadType = getDryadType dryadMap typeDecl 
                let defDeps' = dryadType.defDeps.Add(defName, depFields)
                let newDryadMap = dryadMap.Add(typeDecl.Name, { dryadType with defDeps = defDeps' })
                { env with type2Dryad = newDryadMap }

            let createFld2Fun func env =
                let dryadMap = env.type2Dryad
                let (hdVar, typeDecl) = getParamLocType func
                let dryadType = getDryadType dryadMap typeDecl
                let defDeps = dryadType.defDeps
                let fieldInf' =
                    defDeps |> Map.toList 
                            |> List.map (fun (s, fs) -> (fs |> List.map(fun fld -> (s, fld.Name))))
                            |> List.collect id
                            |> Seq.groupBy snd |> Seq.toList
                            |> List.map (fun (k, sq) -> (k, Seq.toList sq))
                            |> List.map (fun (k, vs) -> (k, vs |> List.map (fun (v, _) -> v) ))
                            |> Map.ofList
                let fieldInf'' = List.fold (fun (m: Map<string, string list>) (fld: Field) -> if m.ContainsKey(fld.Name) then m else m.Add(fld.Name, [])) fieldInf' typeDecl.Fields
                let newDryadMap = dryadMap.Add(typeDecl.Name, { dryadType with fieldInf = fieldInf'' })
                { env with type2Dryad = newDryadMap }
                
            let createReachFun func env = 
                let dryadMap = env.type2Dryad  
                let (hdVar, typeDecl) = getParamLocType func
                let dryadType = getDryadType dryadMap typeDecl
                let baseDefs = dryadType.baseDefs
                let defNames' = dryadType.defNames |> List.filter (fun x -> not(x.Contains("_R")))
                let reachFun' = defNames' 
                                |> List.map (fun x -> (baseDefs.TryFind(x), baseDefs.TryFind(x + "_R")))
                                |> List.filter (fun (nopt, fopt) -> nopt.IsSome && fopt.IsSome)
                                |> List.map (fun (no, fo) -> (no.Value.Name, fo.Value))
                                |> Map.ofList
                let newDryadMap = dryadMap.Add(typeDecl.Name, {dryadType with reachFun = reachFun'})
                {env with type2Dryad = newDryadMap}                
                
            let analyzeDecl(env, d) =
                match d with 
                | Top.TypeDecl td ->
                    if (tdHasAnyDryadAttr td) then 
                        let env' = analyzeDryadTypeDecl (td, env)
                        (env', d)
                    else (env, d)
                | Top.FunctionDecl f -> 
                    if not(f.IsSpec) && funHasDryadAttr "" f   then 
                        analyzeFunction f env
                        (env, d)
                    elif funHasAnyDryadAttr f then 
                        let (|Prefix|_|) (pre: string) (s: string) = if s.StartsWith(pre) then Some(s.Substring(pre.Length)) else None
                        let attrStr = funGetDryadAttr f
                        match attrStr with
                        | Prefix "base:"   defName -> (addToFunMap("base", defName, f, env), d)
                        | Prefix "unfold:" defName -> (analyzeDryadUnfoldFun (defName, f, env), d)
                        | Prefix "same:"   defName -> (addToFunMap("same", defName, f, env), d)
                        | Prefix "cond:"   defName -> (addToFunMap("cond", defName, f, env), d)
                        | Prefix "disj:"   defName -> (addToFunMap("disj", defName, f, env), d)
                        | Prefix "lemma:"  defName -> (addToFunMap("lemma", defName, f, env), d)
                        | Prefix "end" _ ->
                            let env' = env |> createFld2Fun f |> createReachFun f
                            (env', d)
                        | _ as s -> (env, d) 
                    else (env, d)
                | _ -> (env, d)

            let rec mapDecl env f ds = 
                match ds with
                | [] -> []
                | d :: ds' -> 
                    let (env', d') = f(env, d)
                    d :: (mapDecl env' f ds')

            let emptyDeclEnv = { type2Dryad = Map.empty }
            let newDecls = decls |> (mapDecl emptyDeclEnv analyzeDecl)
            newDecls

        // ------------- malloc transformer ---------------------
        let handleMalloc self e =
            match e with
            | Expr.Macro(_, "=", [lexp; rexp])  as mexp ->
                let rexp' = peelCast rexp
                match rexp' with 
                | Expr.Call(_, { Name = "malloc" }, _, _) ->
                    let lexp = self lexp
                    let mkSetUnionStmt (e1 : Expr) (e2 : Expr) = Expr.Call(e1.Common, dryadFunDict.["\oset_union"], [], [e1; e2])
                    let newNotInGlobal = Expr.MkAssume(mkNot(Expr.Call(boolBogusEC(), dryadFunDict.["\oset_in"], [], [lexp; (mkSetUnionStmt globSetPreRef globSetPostRef) ])))
                    let singleLoc   = Expr.Call( { bogusEC with Type = Type.OSet },  dryadFunDict.["\oset_singleton"], [], [lexp])
                    let unionNewLoc = Expr.Call( { bogusEC with Type = Type.OSet },  dryadFunDict.["\oset_union"], [], [globSetPreRef; singleLoc])
                    let addGlobalLoc = Expr.SpecCode(Expr.Macro(bogusEC, "=", [globSetPostRef; unionNewLoc]))
                    let globReachCall = Expr.Call( { bogusEC with Type = Type.OSet }, dryadFunDict.["glob_reach"], [], [])
                    //let equivPostStmt = Expr.MkAssume(mkEq globReachCall globSetPostRef)
                    Some(Expr.MkBlock([ mexp; newNotInGlobal; addGlobalLoc ]))
                | _ -> None
            | _ -> None
              
        let init (helper:TransHelper.TransEnv) = 
            helper.AddTransformer("dryad-begin", TransHelper.DoNothing)
            helper.AddTransformer("dryad-collect-fun", TransHelper.Decl collectDryadFunctions)
            helper.AddTransformer("dryad-analyze", TransHelper.Decl analyzeFunctions)
            helper.AddTransformer("dryad-add-loc-after-malloc", TransHelper.Expr handleMalloc)
            helper.AddTransformer("dryad-end", TransHelper.DoNothing)
