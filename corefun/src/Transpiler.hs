-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Transpiler where

import Ast
import CommonAst
import qualified TransErrors as E

import qualified Data.Map as M
import Data.Maybe
import Data.List
import Data.Char

import Control.Arrow ((&&&), first)

-- First, we transpile an extended program into a semantically equivalent
-- extended program. This equivalent program is ALSO a core program, as a core
-- program is also a valid extended program. Afterwards, we can use conversion
-- functions which map constructs in the extended AST one-to-one with the core
-- AST.

transpile :: ExtendedProgram -> ExtendedProgram
transpile = tProducts
          . tLetIns
          . tVariants
          . tTopFunc
          . tGuards
          . tTypeClasses



{-- TYPECLASSES --}

-- We keep maps of class names to instances of that class.
type ClassMap = M.Map Ident InstanceMap

-- Each instance is then further reduced to a map of the functions which live
-- in that instance, so Class Name -> Instance -> Function
type InstanceMap = M.Map Ident [Func]

--
type InstanceCol = [(Ident, Ident, [Func])]

tTypeClasses :: ExtendedProgram -> ExtendedProgram
tTypeClasses p =
  let inst    = [i | (InstanceDec i) <- p]
      funcs   = [f | (FuncDec f) <- p]
      classes = [c | (ClassDec c) <- p]
      instGroups = groupBy (\i1 i2 -> classInstance i1 == classInstance i2)
                 $ sortBy (\i1 i2 -> classInstance i1 `compare` classInstance i2) inst
      newFuncMap = buildClassMap classes instGroups
      funcs'  = concatMap (expandFunc newFuncMap) funcs
      flatFuncs = mapToFuncs newFuncMap
      funcs'' = map (subOverloaded flatFuncs) funcs'
  in updateFuncs funcs'' flatFuncs p


-- Construct the class map
buildClassMap :: [Class] -> [[Instance]] -> ClassMap
buildClassMap cs =
  foldl (\m is -> M.insert (classInstance $ head is) (buildInstanceMap cs is) m) M.empty

-- Construct the instane map
buildInstanceMap :: [Class] -> [Instance] -> InstanceMap
buildInstanceMap cs =
  foldl (\m i -> M.insert (instanceType i) (instToFuncCollection cs i) m) M.empty

-- We keep the class information at this step to extract the parameter type
-- information. A type class has a free parameter $a$ which we will substitude
-- with the instance type. The function is simply constructed by mixing the
-- parameters, types and instance member body together.
instToFuncCollection :: [Class] -> Instance -> [Func]
instToFuncCollection cs i =
  case find (\c -> className c == classInstance i) cs of
    Nothing -> error . E.classNotDefined $ classInstance i
    Just c ->
      map (\mb ->
        case find (\(mn, _) -> mn == memberName mb) (classMembers c) of
          Nothing -> error $ E.classNoSuchMember (memberName mb) c
          Just (_, s) ->
            let n = Ident $ "__" ++ ident (memberName mb) ++ ident (instanceType i)
                sig = newSig (classVar c) (VrntT (instanceType i) []) s
                b = [(memberParams mb, memberBody mb, Nothing)]
            in Func n [] sig b
      ) $ memberInstances i

-- Use type variable substitution to traverse the class member signature and
-- return a new signature with the instance type inserted instead
newSig :: Ident -> BType -> FType -> FType
newSig tv tname (UnivT u t) | u == tv = newSig tv tname t
newSig tv tname (UnivT u t) = UnivT u $ newSig tv tname t
newSig tv tname (FAncT t1 t2) = FAncT (newSig tv tname t1) (newSig tv tname t2)
newSig tv tname (BAncT t1 t2) = BAncT (tvSub tv tname t1) (newSig tv tname t2)
newSig tv tname (DynT t1 t2) =
  let t1' = tvSub tv tname t1 in case t2 of
    Nothing  -> DynT t1' t2
    Just t2' -> DynT t1' . Just $ tvSub tv tname t2'

-- With the class information converted, we move on to expanding any function
-- which has a context. The context must be removed and the restricted type
-- variables expanded into $n$ copies, one for each instance of the class
-- derived
expandFunc :: ClassMap -> Func -> [Func]
expandFunc _ f@(Func _ [] _ _) = [f]
expandFunc m f@(Func fn rs _ _) =
  let iss = collectInsts rs
      prods = foldr (\xs as -> xs >>= \x -> as >>= \a -> [x : a]) [[]] iss
  in map (newFunc f) prods
  where

    -- Get the set of instances for each restriction in the context
    collectInsts :: [Restriction] -> [InstanceCol]
    collectInsts [] = []
    collectInsts ((c, tv):rs) =
      case M.lookup c m of
        Nothing -> error $ E.contextClassNotDefined fn c
        Just is -> fmap (\(k, i) -> (tv, k, i)) (M.toList is) : collectInsts rs

    -- Takes an inhabitant of the cross product of restrictions placed on the
    -- function. Constructs a new function from this inhabitant
    newFunc :: Func -> InstanceCol -> Func
    newFunc (Func fn _ sig cls) inst =
      let nName = "__" ++ newName inst fn
          nSig = foldl (\sig' (tv, k, i) -> newSig tv (VrntT k []) sig') sig inst
          nClss = map (\(p, e, g) -> (p, newCls inst e, g)) cls
      in Func (Ident nName) [] nSig nClss

    newName :: InstanceCol -> Ident -> String
    newName [] fn = ident fn
    newName ((_, k, _):inst') fn = newName inst' fn ++ ident k

    newCls :: InstanceCol -> Expr -> Expr
    newCls _ Unit = Unit
    newCls _ (Var x) = Var x
    newCls _ (Vrnt v) = Vrnt v
    newCls inst (Inl e) = Inl $ newCls inst e
    newCls inst (Inr e) = Inr $ newCls inst e
    newCls inst (Roll t e) =
      Roll (foldl (\t' (tv, k, _) -> tvSub tv (VrntT k []) t') t inst) (newCls inst e)
    newCls inst (Unroll t e) =
      Unroll (foldl (\t' (tv, k, _) -> tvSub tv (VrntT k []) t') t inst) (newCls inst e)
    newCls inst (Prod es) = Prod $ map (newCls inst) es
    newCls inst (LetIn les e) =
      LetIn (map (fst &&& (newCls inst . snd)) les) (newCls inst e)
    newCls inst (CaseOf e cs) =
      CaseOf (newCls inst e) (map (fst &&& (newCls inst . snd)) cs)
    newCls inst (FunApp fn as es) =
      let (fn', as') = transTypeParams inst as fn
      in FunApp (Ident fn') as' es
    newCls inst (InvApp fn as es) =
      let (fn', as') = transTypeParams inst as fn
      in InvApp (Ident fn') as' es

    -- Translate a function application to remove the restricted type variables
    -- and instead call the appropriate newly generated function (by the naming
    -- convention)
    transTypeParams :: InstanceCol -> [BType] -> Ident -> (String, [BType])
    transTypeParams _ [] fn = (ident fn, [])
    transTypeParams inst (TVar a:as) fn =
      let (fn', as') = transTypeParams inst as fn
      in case find (\(tv, k, i) -> tv == a) inst of
        Nothing -> (fn', TVar a:as')
        Just (tv, k, i) -> case fn' of
          ('_':'_':fn'') -> ("__" ++ fn'' ++ ident k, as')
          fn''           -> ("__" ++ fn'' ++ ident k, as')
    transTypeParams inst (a:as) fn =
      let (fn', as') = transTypeParams inst as fn
      in (fn', a:as')

subOverloaded :: [Func] -> Func -> Func
subOverloaded m f = f { funcClauses = map (\(ps, e, g) -> (ps, sub e, g)) $ funcClauses f }
  where
    sub Unit = Unit
    sub (Var x) = Var x
    sub (Vrnt v) = Vrnt v
    sub (Inl e) = Inl $ sub e
    sub (Inr e) = Inr $ sub e
    sub (Roll t e) = Roll t $ sub e
    sub (Unroll t e) = Unroll t $ sub e
    sub (Prod es) = Prod $ map sub es
    sub (LetIn les e) =
      LetIn (map (fst &&& (sub . snd)) les) (sub e)
    sub (CaseOf e cs) =
      CaseOf (sub e) (map (fst &&& (sub . snd)) cs)
    sub (FunApp fn as es) =
      if classFunc fn m
      then FunApp (Ident $ ident fn ++ overloadedFuncName as) [] es
      else FunApp fn as es
    sub (InvApp fn as es) =
      if classFunc fn m
      then InvApp (Ident $ ident fn ++ overloadedFuncName as) [] es
      else InvApp fn as es

    classFunc fn m = case find (\(Func fn' _ _ _) -> fn == fn') m of
      Nothing -> False
      _       -> True

overloadedFuncName :: [BType] -> String
overloadedFuncName [] = ""
overloadedFuncName (VrntT v []:as') = ident v ++ overloadedFuncName as'
overloadedFuncName as = error $ E.invalidOverloads as

-- Fan out the nested map structure into only the functions at the leaves
mapToFuncs :: ClassMap -> [Func]
mapToFuncs = concatMap snd . concatMap (M.toList . snd) . M.toList

-- Add the newly generated functions as top level declarations and remove the
-- class and instance declarations
updateFuncs :: [Func] -> [Func] -> ExtendedProgram -> ExtendedProgram
updateFuncs fs newFs p = [x | x@(TypeDec _) <- p]
                      ++ [x | x@(CoreFuncDec _) <- p]
                      ++ [x | x@(RecordDec _) <- p]
                      ++ map FuncDec fs
                      ++ map FuncDec newFs



{-- GUARDS --}

tGuards :: ExtendedProgram -> ExtendedProgram
tGuards = map (\d -> case d of
  FuncDec f -> main f
  d' -> d')
  where
    main f = let cls = funcClauses f
                 cls' = sortBy (\(p1, _, _) (p2, _, _) -> compare p1 p2) cls
                 groups = groupBy (\(p1, _, _) (p2, _, _) -> p1 == p2) cls'
                 guardedCls = map (consGuardCls $ funcName f) groups
             in FuncDec $ f { funcClauses = guardedCls }

    consGuardCls f cls =
      if length cls > 1
      then let (params, _, _) = head cls
               e = travCls cls
           in (params, e, Nothing)
      else head cls
      where
        travCls [] = error E.guardForNoClauses
        travCls [(_, e, g)] = case g of
          Nothing -> e
          Just _  -> error $ E.noDefaultGuard f
        travCls ((_, e, g):cls') = case g of
          Nothing -> error E.guardOmitted
          Just g' -> CaseOf g' [(Inl Unit, e), (Inr Unit, travCls cls')]



{-- TRANSPILING TOP LEVEL CASE --}

data Tree = Node Expr [Tree]
          | Leaf Expr Expr
          deriving (Show)

-- We will work on an $N x M$ double list of expressions, which correspond to
-- $N$ number of clauses each with $M$ parameters.
type Parameters = [[Expr]]

-- Sname as a clause, but without guards, they have been translated already at
-- this point
type SimpleClause = ([Expr], Expr)

tTopFunc :: ExtendedProgram -> ExtendedProgram
tTopFunc p = map (\d -> case d of
  FuncDec f -> CoreFuncDec $ main f
  d' -> d') p
  where
    main f =
      let (unis, ft)  = getUnis (funcSig f)
          paramTypes  = getParams ft
          params      = map (\(ps, _, _) -> ps) $ funcClauses f
          bodies      = map (\(_, fe, _) -> fe) $ funcClauses f
          paramNames  = generateParamNames (length paramTypes) params []
          tags        = tagParamsForUnroll 0 (length paramTypes - 1) params
          _           = checkNamingInvariant $ zip tags (transpose params)
          unfoldTypes = map snd . filter fst $ zip tags paramTypes
          unfoldNames = map snd . filter fst $ zip tags paramNames
          unfoldParms = filterUnfolds tags params
          tree        = buildTree . sortBy (\x y -> compare (fst x) (fst y))
                          $ zip (sort unfoldParms) bodies
          body = case bodies of
            [b] -> b
            _ -> collapseClauses unfoldTypes unfoldNames tree
      in CoreFunc (funcName f) unis (zip paramNames paramTypes) body

    -- Get the list of universal type variables and return the remaining
    -- signature type
    getUnis :: FType -> ([Ident], FType)
    getUnis (UnivT i ft) = let (unis', ft') = getUnis ft in (i : unis', ft')
    getUnis ft = ([], ft)

    -- Get the remaining signature types as a list
    getParams :: FType -> [AType]
    getParams (FAncT t1 t2) = AFType t1 : getParams t2
    getParams (BAncT t1 t2) = ABType t1 : getParams t2
    getParams (DynT  t1 _)  = [ABType t1]

    -- Register which parameter indices in the clauses need to be made into a
    -- case-expression (returns a flag list of indices)
    tagParamsForUnroll :: Int -> Int -> Parameters -> [Bool]
    tagParamsForUnroll n lst pss =
      let tag = tryTag False $ map (!! n) pss
      in if n == lst then [tag] else tag : tagParamsForUnroll (n+1) lst pss
      where
        tryTag t []         = t
        tryTag t (Var _:ps) = tryTag t ps
        tryTag _ (_:ps)     = tryTag True ps

    -- Use the flag list to retrieve the parameters which need to be made into
    -- a case-expression (hence called unfolding)
    filterUnfolds :: [Bool] -> Parameters -> Parameters
    filterUnfolds [] params | null (head params) = params
    filterUnfolds (t:tags) params =
      let params' = map tail params
          rest = filterUnfolds tags params'
      in if not t
         then rest
         else map (\(pa, r) -> head pa : r) $ zip params rest

    -- For each parameter which needs to get unfolded, try to get a variable
    -- name from the form of the parameter (should one be called (Succ n0) for
    -- example, try to get the name n0), otherwise get a fresh name. Prefix it
    -- with '!' to avoid name clashes
    generateParamNames :: Int -> Parameters -> [Maybe Ident] -> [Ident]
    generateParamNames 0 _ suggestions =
      let paired = zip ['a'..] suggestions
      in map (\(v, pa) -> fromMaybe (Ident $ '~' : [v]) pa) paired
    generateParamNames n params suggestions =
      let name = tryGenerate params
          suggestions' = name : suggestions
      in generateParamNames (n-1) params suggestions'
      where
        tryGenerate [] = Nothing
        tryGenerate (paramExprs:params') =
          case paramExprs !! (n-1) of
            Var x -> Just x
            _     -> tryGenerate params'

    -- Make sure that variables which do not change do not change name either.
    -- This makes it simpler to get a name for them (as otherwise we would have
    -- to pick one at random and rewrite the clauses to make them homogenous)
    checkNamingInvariant :: (Eq a, Show a) => [(Bool, [a])] -> ()
    checkNamingInvariant [] = ()
    checkNamingInvariant ((t, ps):pts) | t || all (== head ps) ps =
      checkNamingInvariant pts
    checkNamingInvariant ((_, ps):_) = error $ E.namesNotInvariant ps

    -- Turn the clauses into an intermediary representation: A tree which
    -- mirrors the form of the resulting case expression pretty well. It is a
    -- list of trees as the root is missing. We don't need it here, as it is
    -- added when the case-expressions is constructed
    buildTree :: [SimpleClause] -> [Tree]
    buildTree pss | length (fst (head pss)) == 1 =
      map (\([ps], fe) -> Leaf ps fe) pss
    buildTree pss =
      let tier = groupBy (\(ps1, _) (ps2, _) -> head ps1 == head  ps2) pss
      in map (\pss' ->
        let ex = head . fst $ head pss'
            leafs = map (Control.Arrow.first tail) pss'
        in Node ex $ buildTree leafs
      ) tier

    -- Finally, use the tree to Construct the case expressions. If the type of
    -- any parameter which needs to unfolded is not a sum or variant type (so
    -- in essence, a sum type), we cannot unfold it and raise an error
    collapseClauses :: [AType] -> [Ident] -> [Tree] -> Expr
    collapseClauses [t] [n] tree =
      let arms = map (\(Leaf e fe) -> (e, fe)) tree
          cas = case t of
            ABType (SumT _ _)  -> Var n
            ABType x@(VrntT v _) | isVrntRec p v -> Unroll x (Var n)
            ABType (VrntT _ _) -> Var n
            ABType t'          -> error $ E.clauseExprIllFormed t'
        in CaseOf cas arms
    collapseClauses (t:ts) (n:ns) tree =
      let arms = map (\(Node e tree') -> (e, collapseClauses ts ns tree')) tree
          cas = case t of
            ABType (SumT _ _)  -> Var n
            ABType x@(VrntT v _) | isVrntRec p v -> Unroll x (Var n)
            ABType (VrntT _ _) -> Var n
            ABType t'          -> error $ E.clauseExprIllFormed t'
      in CaseOf cas arms



{-- TRANSPILING VARIANTS --}

--
type TransType = ([Ident], BType)

type SimpleType = (Ident, TransType)

-- Functions as reader environment payload (no monads used though.) Searchable
-- by variant constructor through variant declaration
type PairedDec = (Declaration, SimpleType)

-- Top level variant translation
tVariants :: ExtendedProgram -> ExtendedProgram
tVariants p = let tdecs = [d | d@(TypeDec _) <- p]
                  simpleDecs = map tDataDec tdecs
                  pairedDecks = zip tdecs simpleDecs
              in map (tParams pairedDecks
                    . tCases pairedDecks) p

-- Transforms a variant declaration into a simple type, where the name of the
-- variant, the name of the type variables it has and finally the converted
-- ground type
tDataDec :: Declaration -> SimpleType
tDataDec (TypeDec (DataType n as vrnts)) = let bt = toBType n vrnts
                                           in (n, (as, bt))

toBType :: Ident -> [TypeCons Ident] -> BType
toBType n vrnts = case trav vrnts of
  (t, Nothing) -> t
  (t, Just i) -> RecT i t
  where

    -- Builds up a sum type of the variant constructors. Also propagates the
    -- idea whether the type should be recursive through the second tuple
    -- element $i$
    trav :: [TypeCons Ident] -> (BType, Maybe Ident)
    trav [TypeCons _ v] = tVarEntry v
    trav (TypeCons _ v:vrnts') =
      let (t1, rec1) = tVarEntry v
          (t2, rec2) = trav vrnts'
          rec = case (rec1, rec2) of
            (i@(Just _), _) -> i
            (_, i@(Just _)) -> i
            (_, _) -> Nothing
      in (SumT t1 t2, rec)

    -- Traverses a particular variant constructors type parameters to build up
    -- its type. Also propagates whether the final type should be recursive
    tVarEntry :: [ConsParam Ident] -> (BType, Maybe Ident)
    tVarEntry [] = (UnitT, Nothing)
    tVarEntry [p] =
      case p of
        TypeVar a -> (TVar a, Nothing)
        ConsInner it -> case it of
          TypeCons ni ics | n == ni -> case ics of
            [] -> (TVar (Ident "X"), Just (Ident "X"))
            [TypeVar _] -> (TVar (Ident "X"), Just (Ident "X"))
            vv -> error $ E.onlySimpleConstructors vv
          TypeCons ni _ -> error $ E.onlyRecursiveInnerVariants ni
    tVarEntry ps = let ts = map (\p -> tVarEntry [p]) ps
                       rec = filter isJust (map snd ts)
                       ret_t = ProdT (map fst ts)
                   in case rec of
                     [] -> (ret_t, Nothing)
                     (Just i:_) -> (ret_t, Just i)

-- Main transformation of any function body containing variants into one
-- without them Note that it assumes that top-level cases have been transformed
-- first, as it only operates on core function declarations
tCases :: [PairedDec] -> Declaration -> Declaration
tCases s dec = case dec of
  CoreFuncDec f -> CoreFuncDec $ tCoreFuncCases f
  d             -> d
  where
    tCoreFuncCases (CoreFunc f u p e) = CoreFunc f u p $ tExprCases e
    tExprCases Unit = Unit
    tExprCases (Var x) = Var x
    tExprCases (Roll t e) = Roll (tSimpleType s t) (tExprCases e)
    tExprCases (Unroll t e) = Unroll (tSimpleType s t) (tExprCases e)
    tExprCases (Inl e) = Inl $ tExprCases e
    tExprCases (Inr e) = Inr $ tExprCases e
    tExprCases (Prod es) = Prod $ map tExprCases es
    tExprCases (Vrnt v) = tVariantExpr s v
    tExprCases (FunApp f ts es) = FunApp f ts $ map tExprCases es
    tExprCases (InvApp f ts es) = InvApp f ts $ map tExprCases es
    tExprCases (LetIn les e) =
      LetIn (map (fst &&& (tExprCases . snd)) les) (tExprCases e)
    tExprCases (CaseOf e cs) =
      let e' = tExprCases e
      in case head cs of
        (Vrnt (TypeCons n _), _) -> let pcs = getVrntDec s n
                                    in travCases e' ['A'..] $ orderCases pcs cs
        _ -> CaseOf e cs

    -- Order the variant constructors in the case so that they line up the the
    -- declaration. Also make some sanity checks regarding the left-hand case
    -- arms: Make sure only the variant constructors appear.
    orderCases :: [TypeCons Ident] -> [(Expr, Expr)] -> [(Expr, Expr)]
    orderCases [] _ = []
    orderCases (TypeCons n _:pcs') cs =
      case find (\(Vrnt (TypeCons cn _), _) -> cn == n) cs of
        Nothing -> error $ E.variantCaseMissing n
        Just x  -> x : orderCases pcs' cs

    -- Tranlate the variant case into an equivalent core sum-term case
    travCases :: Expr -> String -> [(Expr, Expr)] -> Expr
    travCases _ _ []  = error E.caseNoBranches
    travCases _ _ [_] = error E.caseOneBranch
    travCases e' _ [(Vrnt (TypeCons _ ps1), e1)
                  , (Vrnt (TypeCons _ ps2), e2)] =
      let l1 = tVariantParams ps1
          l2 = tVariantParams ps2
          e1' = tExprCases e1
          e2' = tExprCases e2
      in CaseOf e' [(Inl l1, e1'), (Inr l2, e2')]
    travCases e' (f:fs') ((Vrnt (TypeCons _ ps), e1):cs') =
      let l1 = tVariantParams ps
          l2 = Var (Ident (show f))
          e1' = tExprCases e1
          e2' = travCases l2 fs' cs'
      in CaseOf e' [(Inl l1, e1'), (Inr l2, e2')]

    -- Transform a variant constructor's parameters into the equivalent core
    -- expression
    tVariantParams :: [ConsParam Expr] -> Expr
    tVariantParams [] = Unit
    tVariantParams [TypeVar x] = x
    tVariantParams ps = Prod [x | (TypeVar x) <- ps]

    -- Translates any variant constructor directly into its equivalent core
    -- representation.
    tVariantExpr :: [PairedDec] -> TypeCons Expr -> Expr
    tVariantExpr s (TypeCons n ps) =
      let vs = getVrntDec s n
      in trans vs
      where
        trans [] = error E.constructorWrong
        trans [tc] = if n == consName tc
                     then tVariantParams ps
                     else trans []
        trans (tc:vs') = if n == consName tc
                         then Inl $ tVariantParams ps
                         else Inr $ trans vs'

-- Transforms the types of a function's parameters from one which may contain
-- variant types to one without variant types
tParams :: [PairedDec] -> Declaration -> Declaration
tParams s dec = case dec of
  CoreFuncDec f -> CoreFuncDec (f { coreFuncParams = map tParam (coreFuncParams f) })
  d             -> d
  where
    tParam (i, ABType t) = (i, ABType $ transBParam t)
    tParam (i, AFType t) = (i, AFType $ transFParam t)
    transBParam v@(VrntT _ _) = tSimpleType s v
    transBParam (ProdT ts) = ProdT $ map transBParam ts
    transBParam (SumT t1 t2) = SumT (transBParam t1) (transBParam t2)
    transBParam t = t
    transFParam (UnivT u t) = UnivT u $ transFParam t
    transFParam (FAncT t1 t2) = FAncT (transFParam t1) (transFParam t2)
    transFParam (BAncT t1 t2) = BAncT (transBParam t1) (transFParam t2)
    transFParam (DynT t1 t2) =
      let t1' = transBParam t1
      in case t2 of
        Nothing -> DynT t1' t2
        Just t2' -> DynT t1' (Just $ transBParam t2')

-- Translates any type into an equivalent ground type. Handles nested recursion
-- properly.
tSimpleType :: [PairedDec] -> BType -> BType
tSimpleType tDecs t = let t' = get tDecs t
                      in fixRec ['A'..] t'
  where
    get tDecs (VrntT v ps) =
      case find (\(i, _) -> i == v) (map snd tDecs) of
        Nothing -> error $ E.variantNotDefined v
        Just (_, (tvs, t)) ->
          foldl (\t' (tv, p) ->
            let pt = get tDecs p
            in tvSub tv pt t') t $ zip tvs ps
    get tDecs (ProdT ts) = ProdT $ map (get tDecs) ts
    get tDecs (SumT t1 t2) = SumT (get tDecs t1) (get tDecs t2)
    get tDecs (RecT x t) = RecT x $ get tDecs t
    get _ t = t

-- Make sure that nested recursive variants are assigned unique recursion
-- varables (prepended with "--" to avoid name clashes.
fixRec rs UnitT = UnitT
fixRec rs (TVar a) = TVar a
fixRec rs (ProdT ts) = ProdT $ map (fixRec rs) ts
fixRec rs (SumT t1 t2) = SumT (fixRec rs t1) (fixRec rs t2)
fixRec (r:rs) (RecT a t) =
  let t' = fixRec rs t
      rv = Ident [r]
  in RecT rv $ tvSub a (TVar rv) t'

-- Gets a variant declaration from the reader environment based on the name of
-- variant constructor
getVrntDec :: [PairedDec] -> Ident -> [TypeCons Ident]
getVrntDec tDecs n =
  case find (\d -> case d of
                     TypeDec (DataType _ _ vs) -> isAlternative n vs
                     _ -> False) (map fst tDecs) of
  Just (TypeDec (DataType _ _ d))  -> d
  _ -> error $ E.variantConstructorUnknown n
  where
    isAlternative _ [] = False
    isAlternative i (TypeCons i' _:_) | i == i' = True
    isAlternative i (_:vs') = isAlternative i vs'

tvSub' tv newT UnitT = UnitT
tvSub' tv newT (TVar a) | tv == a = newT
tvSub' tv newT (TVar a) = TVar a
tvSub' tv newT (ProdT ts) = ProdT $ map (tvSub' tv newT) ts
tvSub' tv newT (SumT t1 t2) = SumT (tvSub' tv newT t1) (tvSub' tv newT t2)
tvSub' tv newT (RecT a t) = RecT a $ tvSub' tv newT t
tvSub' tv newT (VrntT v ts) = VrntT v $ map (tvSub' tv newT) ts



{-- DYNAMICALLY SIZED PRODUCTS --}

tProducts :: ExtendedProgram -> ExtendedProgram
tProducts = map (\d -> case d of
  CoreFuncDec f@(CoreFunc _ _ _ fe) -> CoreFuncDec $ f { coreFuncBody = tProdFunc ['a' ..] fe }
  d' -> d')
  where
    tProdFunc ns (Inr e) = Inr $ tProdFunc ns e
    tProdFunc ns (Inl e) = Inl $ tProdFunc ns e
    tProdFunc ns (Roll t e) = Roll t $ tProdFunc ns e
    tProdFunc ns (Unroll t e) = Unroll t $ tProdFunc ns e
    tProdFunc ns (CaseOf e les) =
      CaseOf (tProdFunc ns e) (map (tProdCase ns) les)
      where
        tProdCase (n:ns) (Inl (Prod es), ce) =
          let nv = Ident ('_' : [n])
          in (Inl (Var nv), tProdFunc ns $ LetIn [(VarList $ map (\(Var x) -> x) es, Var nv)] ce)
        tProdCase (n:ns) (Inr (Prod es), ce) =
          let nv = Ident ('_' : [n])
          in (Inr (Var nv), tProdFunc ns $ LetIn [(VarList $ map (\(Var x) -> x) es, Var nv)] ce)
        tProdCase ns (e, ce) = (e, tProdFunc ns ce)
    tProdFunc ns (FunApp f ts es) = FunApp f ts $ map (tProdFunc ns) es
    tProdFunc ns (Prod es) = unwrap $ map (tProdFunc ns) es
      where
        unwrap [e1, e2] = Prod [e1, e2]
        unwrap (e1:es') = Prod [e1, unwrap es']
    tProdFunc ns (LetIn [(VarList ls, e)] eout) = trav ns ls e
      where
        trav ns' [l1, l2] e' = LetIn [(VarList [l1, l2], e')] $ tProdFunc ns' eout
        trav (n:ns') (l1:ls) e' = LetIn [(VarList [l1, Ident ('_' : [n])], e')]
                                       (trav ns' ls (Var (Ident ('_' : [n]))))
    tProdFunc ns' (LetIn [(LVar x, e)] eout)= LetIn [(LVar x, tProdFunc ns' e)]
                                                    (tProdFunc ns' eout)
    tProdFunc _ e' = e'

    tProdType (SumT t1 t2) = SumT (tProdType t1) (tProdType t2)
    tProdType (RecT x t) = RecT x $ tProdType t
    tProdType (ProdT ts) = trav ts
      where
        trav [t1, t2] = ProdT [t1, t2]
        trav (t1:ts') = ProdT [t1, trav ts']
    tProdType t = t



{-- ROLL OUT LET EXPRESSIONS --}

tLetIns :: ExtendedProgram -> ExtendedProgram
tLetIns = map (\d -> case d of
  CoreFuncDec f@(CoreFunc _ _ _ e) -> CoreFuncDec $ f { coreFuncBody = tLetIn e }
  d' -> d')
  where
    tLetIn (Inr e) = Inr $ tLetIn e
    tLetIn (Inl e) = Inl $ tLetIn e
    tLetIn (Roll t e) = Roll t $ tLetIn e
    tLetIn (Unroll t e) = Unroll t $ tLetIn e
    tLetIn (CaseOf e les) =
      CaseOf (tLetIn e) (map (fst &&& (tLetIn . snd)) les)
    tLetIn (FunApp f ts es) = FunApp f ts $ map tLetIn es
    tLetIn (InvApp f ts es) = InvApp f ts $ map tLetIn es
    tLetIn (Prod es) = Prod $ map tLetIn es
    tLetIn (LetIn les eout) = trav les
      where
        trav [(l, ein)] = LetIn [(l, ein)] (tLetIn eout)
        trav ((l, ein):les') = let inner = trav les'
                               in LetIn [(l, ein)] inner
    tLetIn Unit = Unit
    tLetIn (Var x) = Var x

{-- == WILL NOT BE DONE == --}

{-- RECORDS --}

-- * Translate types. Need record definitions.
-- * During a direct record translation, decide the order from a the record
--   definition and then construct the product.
-- * For a within block, do the following: Decide on unique names for the full
--   decomposition of the record. The decomposition can be decided from the type.
--   FFS. How do I figure that out? Need a store of types to variables, which
--   isn't possible at this stage. I could restrict records to only operate on
--   parameters to the function? Or to parameters + the ones defined in previously in
--   the body.

-- tRecords :: ExtendedProgram -> ExtendedProgram
-- tRecords p = p



{-- HELPER FUNCTIONS --}

-- Lookup between variant declarations and check if the variant is recursive
-- (it has itself as a variant constructor parameter)
isVrntRec :: ExtendedProgram -> Ident -> Bool
isVrntRec p v = let tdecs = [d | d@(TypeDec _) <- p]
                    simpleDecs = map tDataDec tdecs
                    (_, (_, t)) = fromJust $ find (\(i, _) -> i == v) simpleDecs
                in case t of
                  RecT _ _ -> True
                  _        -> False

-- Takes a type variable and substitudes a ground type for each occurence of
-- that variable in a target type
tvSub :: Ident -> BType -> BType -> BType
tvSub tv newT UnitT = UnitT
tvSub tv newT (TVar a) | tv == a = newT
tvSub tv newT (TVar a) = TVar a
tvSub tv newT (ProdT ts) = ProdT $ map (tvSub tv newT) ts
tvSub tv newT (SumT t1 t2) = SumT (tvSub tv newT t1) (tvSub tv newT t2)
tvSub tv newT (RecT a t) = RecT a $ tvSub tv newT t
tvSub tv newT (VrntT v ts) = VrntT v $ map (tvSub tv newT) ts
