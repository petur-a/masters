{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TypeChecker where

import Core.CoreAst
import CommonAst
import qualified Errors as E

import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Function (on)
import Data.Ord (comparing)

import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

-- DATA TYPES

-- Discerns whether a program was typeable
type TCResult a = Either String a

-- VarEnv is the dual typing environment,
type DynEnv = M.Map String BType
type AncEnv = M.Map String AType

data VarEnv = VarEnv { anc :: AncEnv
                     , dyn :: DynEnv
                     , counter :: String }
            deriving (Eq, Show)

-- FunEnv is the implicit function map
type FunEnv = M.Map String Func

-- Function output type variables constraints
type Constraint = (Ident, BType)

-- Main monad while evaluating a function clause with a variable name state and
-- a read-only function name environment and a write-only constraint set.
newtype TC a = Eval { runEval :: StateT VarEnv
                                (WriterT [Constraint]
                                (ReaderT FunEnv
                                (Except String))) a }
  deriving (Applicative, Functor, Monad, MonadReader FunEnv, MonadState VarEnv,
            MonadError String, MonadWriter [Constraint])

-- TYPECHECKER RUNNING

-- `a` is a type checker function
runTC :: TC a -> VarEnv -> FunEnv -> TCResult ((a, VarEnv), [Constraint])
runTC eval venv fenv = runExcept
                      (runReaderT
                      (runWriterT
                      (runStateT (runEval eval) venv)) fenv)

-- Main typechecker entry
typecheck :: CoreProgram -> Either String [Constraint]
typecheck p = let tc = runTC (checkProg p) initVarEnv (makeFunEnv p)
              in case tc of
                Left e -> Left e
                Right (((), _), constrains) -> solveConstraints constrains

-- TYPECHECKER FUNCTIONS

checkProg :: CoreProgram -> TC ()
checkProg = mapM_ (\f -> do env <- get
                            let cons = counter env
                            put $ VarEnv M.empty M.empty cons
                            checkFunc f)

checkFunc :: Func -> TC ()
checkFunc f = case funcParams f of
  []          -> throwError "Function of nil arity not allowed"
  [(i, t)]    -> case t of
                   ABType t' -> do addDyn i t'
                                   ret_t <- checkExpr (funcBody f)
                                   tell [(funcName f, ret_t)]
                                   return ()
                   _         -> throwError $ E.illegalDynParam f
  ((i, t):ps) -> case t of
    (AFType ft) ->
      do fenv <- ask
         if ident i `M.member` fenv
         then throwError $ E.functionShadowed i
         else do (fn, ret) <- funArgToFun i ft
                 local (M.insert (ident i) fn)
                   $ addAncillae i t >> checkFunc (f { funcParams = ps })
    (ABType _) -> addAncillae i t >> checkFunc (f { funcParams = ps })

checkExpr :: Expr -> TC BType
checkExpr Unit = isDynEmpty >> return UnitT

checkExpr (Var i) =
  do dynL <- dynLookup i
     case dynL of
       Just t -> isDynExact i >> return t
       Nothing ->
         do ancL <- ancillaeLookup i
            case ancL of
              Nothing -> throwError $ E.varNotBound i
              Just t  -> isDynEmpty >>
                         case t of
                           AFType _  -> throwError $ E.illegalFunctionType i
                           ABType t' -> return t'

checkExpr (Inl e) =
  do t <- checkExpr e
     var <- getFreshConsVar
     return $ SumT t var

checkExpr (Inr e) =
  do t <- checkExpr e
     var <- getFreshConsVar
     return $ SumT var t

checkExpr (Prod e1 e2) =
  do (env1, env2) <- getSplitEnvironments [e1] [e2]
     setDyn env1
     t <- checkExpr e1
     setDyn env2
     t' <- checkExpr e2
     return $ ProdT t t'

checkExpr (LetIn l e1 e2) =
  do (env1, env2) <- getSplitEnvironments [e1] [e2]
     setDyn env1
     lt <- checkExpr e1
     setDyn env2
     case (l, lt) of
         (LVar x, t') ->
           do addVar x e2 t' env1
              checkExpr e2
         (VarTuple x y, UVar c) ->
           do var1 <- getFreshConsVar
              var2 <- getFreshConsVar
              tell [(c, ProdT var1 var2)]
              addVar x e2 var1 env1
              addVar y e2 var2 env1
              checkExpr e2
         (VarTuple x y, ProdT t' t'') ->
           do addVar x e2 t' env1
              addVar y e2 t'' env1
              checkExpr e2
         (VarTuple x y, t') -> throwError $ E.badAssignment x y t'

checkExpr (InvLet e e1 e2) =
  do (env1, env2) <- getSplitEnvironments [e1] [e2]
     setDyn env1
     t1 <- checkExpr e1
     setDyn M.empty
     t <- checkExpr e
     if t == t1
     then do setDyn env2
             checkExpr e2
     else throwError $ "Expressions in inverse applications do not match: " ++
                       show t ++ " and " ++ show t1

checkExpr (CaseOf e1 (x, e2) (y, e3) _) = do
  (env1, tenv) <- getSplitEnvironments [e1] [e2, e3]
  setDyn env1
  sum_t <- checkExpr e1
  setDyn tenv
  (env2, env3) <- getSplitEnvironments [e2] [e3]
  case sum_t of
    SumT t' t'' ->
      do setDyn env2
         case x of
           Inl (Var i) -> addVar i e2 t' env1
           _           -> return ()
         t1 <- checkExpr e2
         setDyn env3
         case y of
           Inr (Var i) -> addVar i e3 t'' env1
           _           -> return ()
         t2 <- checkExpr e3
         if t1 == t2
         then
           case (t1, t2) of
             (SumT t1' uv2@(UVar c2), SumT uv1@(UVar c1) t2') ->
               do tell [(c1, t1')]
                  tell [(c2, t2')]
                  return $ SumT uv1 uv2
             _ -> return t1
           else throwError $ E.caseTypesDontMatch t1 t2
    UVar c ->
      do var1 <- getFreshConsVar
         var2 <- getFreshConsVar
         tell [(c, SumT var1 var2)]
         setDyn env2
         case x of
           Inl (Var i) -> addVar i e2 var1 env1
           _           -> return ()
         t1 <- checkExpr e2
         setDyn env2
         case y of
           Inr (Var i) -> addVar i e2 var2 env1
           _           -> return ()
         t2 <- checkExpr e3
         if t1 == t2
         then return t1
         else throwError $ E.caseTypesDontMatch t1 t2
    t -> throwError $ E.caseNotSum t

checkExpr (FunApp fn ts es) =
  do f <- funLookup fn
     case f of
       Nothing -> throwError $ E.functionDoesntExist fn
       Just f'  -> do ps <- checkTypeVars f' ts
                      checkParams (funcName f') ps es

checkExpr (InvApp fn ts es) =
  do f <- funLookup fn
     case f of
       Nothing -> throwError $ E.functionDoesntExist fn
       Just f'  -> do ps <- checkTypeVars f' ts
                      checkInvParams (funcName f') ps es

checkExpr (Unroll ut@(RecT x t') e) =
  do t <- checkExpr e
     case t of
       tv@(UVar c) -> do tell [(c, ut)]
                         return tv
       _ | t == ut -> substitude x t' ut
       _ -> throwError $ E.unrollTypeMismatch t ut
checkExpr (Unroll t _) = throwError $ E.unrollNotRecursive t

checkExpr (Roll rt@(RecT x t') e) =
  do t <- checkExpr e
     sub_t <- substitude x t' rt
     case sub_t of
       tv@(UVar c) -> do tell [(c, rt)]
                         return tv
       _ | t == sub_t -> return rt
       _ -> throwError $ E.rollTypeMismatch t sub_t
checkExpr (Roll t _) = throwError $ E.rollNotRecursive t

checkTypeVars :: Func -> [BType] -> TC [Param]
checkTypeVars f ts = checkTV (funcUnis f) ts (funcParams f)
  where
    checkTV [] [] ps = return ps
    checkTV [] _ _   = throwError $ E.tooManyTypeArgs (funcName f)
    checkTV _ [] _   = throwError $ E.tooFewTypeArgs (funcName f)
    checkTV (tv:tvs) (t:ts') ps = do ps' <- mapM (sub tv t) ps
                                     checkTV tvs ts' ps'
    sub :: Ident -> BType -> Param -> TC Param
    sub tv t (p, ABType (TVar tv')) | tv == tv' = return (p, ABType t)
    sub _ _ p = return p

checkParams :: Ident -> [Param] -> [Expr] -> TC BType
checkParams f [] [] = return $ UVar f
checkParams f ps [] = throwError $ E.tooFewArgs f ps
checkParams f [] es = throwError $ E.tooManyArgs f es
checkParams f pss@(p:ps) ess@(e:es) = do _ <- check f pss ess
                                         checkParams f ps es

checkInvParams :: Ident -> [Param] -> [Expr] -> TC BType
checkInvParams f [(pn, t)] [e] =
  do  t' <- check f [(pn, ABType (UVar f))] [e]
      case t of
        (ABType bt) -> return bt
        at -> throwError $ E.expectedGroundType at
checkInvParams f ps [] = throwError $ E.tooFewArgs f ps
checkInvParams f [] es = throwError $ E.tooManyArgs f es
checkInvParams f pss@(p:ps) ess@(e:es) = do _ <- check f pss ess
                                            checkInvParams f ps es

check :: Ident -> [(Ident, AType)] -> [Expr] -> TC BType
check f ((pn, t):ps) (Var i:es) =
  do ancL <- ancillaeLookup i
     case ancL of
       Just t' ->
         do (env1, env2) <- getSplitEnvironments [] es
            setDyn env1
            isDynEmpty
            setDyn env2
            compareTypes pn t t' f
            return UnitT
       Nothing ->
         do fnL <- funLookup i
            case fnL of
              Just _ ->
                do (env1, env2) <- getSplitEnvironments [] es
                   setDyn env1
                   isDynEmpty
                   setDyn env2
                   tell [(i, UVar f)]
                   compareTypes pn t (ABType (UVar f)) f
                   return UnitT
              Nothing ->
                do (env1, env2) <- getSplitEnvironments [Var i] es
                   setDyn env1
                   dynL <- dynLookup i
                   case dynL of
                     Just t' ->
                       do isDynExact i
                          case t of
                            abt@(ABType _) ->
                              do setDyn env2
                                 compareTypes pn abt (ABType t') f
                                 return t'
                            a -> throwError $ E.expectedGroundType a
                     Nothing -> throwError $ E.varNotBound i
check f ((pn, t):ps) (e:es) =
  case t of
    (ABType t') ->
      do (env1, env2) <- getSplitEnvironments [e] es
         setDyn env1
         te <- checkExpr e
         setDyn env2
         compareTypes pn (ABType t') (ABType te) f
         return te
    at -> throwError $ E.expectedGroundType at

compareTypes :: Ident -> AType -> AType -> Ident -> TC ()
compareTypes _ (ABType t) (ABType (UVar c)) f =
  do tell [(c, t)]
     return ()
compareTypes pn t t' f =
  if t === t'
  then return ()
  else throwError $ E.wrongArgType f pn t t'
  where
    (===) (ABType t1) (ABType t2) = t1 `laxEq` t2
    (===) t1 t2 = t1 == t2

laxEq :: BType -> BType -> Bool
laxEq (TVar _) (TVar _) = True
laxEq (ProdT t1 t2) (ProdT t1' t2') = t1 `laxEq` t1' && t2 `laxEq` t2'
laxEq (SumT t1 t2) (SumT t1' t2') = t1 `laxEq` t1' && t2 `laxEq` t2'
laxEq (RecT _ t) (RecT _ t') = t `laxEq` t'
laxEq t1 t2 = t1 == t2

-- DYNAMIC SPLIT ANALYSIS

getSplitEnvironments :: [Expr] -> [Expr] -> TC (DynEnv, DynEnv)
getSplitEnvironments es1 es2 = do
  env <- get
  let s1 = M.filterWithKey (\x _ -> x `elem` splitAnalysis es1) (dyn env)
  let s2 = M.filterWithKey (\x _ -> x `elem` splitAnalysis es2) (dyn env)
  let rmg = dyn env `M.difference` (s1 `M.union` s2)
  return (s1 `M.union` rmg, s2 `M.union` rmg)

-- Return the set of dynamic variables used in any of a list of expressions
splitAnalysis :: [Expr] -> [String]
splitAnalysis = map ident . nub . split
  where
    split = foldl (\s e -> s ++ split' e) []
    split' (Var i) = [i]
    split' Unit = []
    split' (Inl e) = split' e
    split' (Inr e) = split' e
    split' (Prod e e') = split' e ++ split' e'
    split' (LetIn _ e e') = split' e ++ split' e'
    split' (InvLet _ e e') = split' e ++ split' e'
    split' (CaseOf e (_, e1) (_, e2) _) = split' e ++ split' e1 ++ split' e2
    split' (FunApp _ _ es) = split' $ last es
    split' (InvApp _ _ es) = split' $ last es
    split' (Roll _ e) = split' e
    split' (Unroll _ e) = split' e

-- Make sure that a variable name bound to in a let and case request is used
guaranteeNewUsed :: Ident -> Expr -> TC ()
guaranteeNewUsed i e = if grnt e
                       then return ()
                       else throwError $ E.newVarNotUsed i
  where
    grnt (Var i') | ident i == ident i' = True
    grnt (Var i') | ident i /= ident i' = False
    grnt Unit = False
    grnt (Inl e1) = grnt e1
    grnt (Inr e1) = grnt e1
    grnt (Prod e1 e2) = grnt e1 || grnt e2
    grnt (LetIn x e1 e2) = grnt e1 || grnt e2
    grnt (CaseOf es (_, e1) (_, e2) _) = grnt es || grnt e1 || grnt e2
    grnt (FunApp _ _ es) = foldl (\t ep -> t || grnt ep) False es
    grnt (InvApp _ _ es) = foldl (\t ep -> t || grnt ep) False es
    grnt (Roll _ e1) = grnt e1
    grnt (Unroll _ e1) = grnt e1

-- CONSTRAINT SOLVING

getFreshConsVar :: TC BType
getFreshConsVar = do cnt <- nextUVar
                     modify $ \env -> env { counter = cnt }
                     return . UVar $ Ident cnt

nextUVar :: TC String
nextUVar = do env <- get
              let cnt = counter env
              if last cnt == 'Z'
              then return $ cnt ++ ['A']
              else return $ init cnt ++ [succ $ last cnt]

solveConstraints :: [Constraint] -> Either String [Constraint]
solveConstraints cons =
  let grouped = map (\l -> (fst . head $ l, nubBy laxEq $ map snd l))
                  . groupBy ((==) `on` fst)
                  $ sortBy (comparing fst) cons
      wrong = filter (\(_, cs) -> length cs > 1) grouped
      wrongMes = foldl (\s1 (n, cs) -> s1 ++ ident n ++ " - Clashing candidates are: " ++
                   foldl (\s2 c -> s2 ++ show c ++ ", ") "" cs) "" wrong
  in case wrongMes of
    "" -> Right cons
    w -> Left $ "Constrains failed for the following functions: " ++ w
                ++ "\nThe full set of constraints: " ++ show cons

-- -- HELPER FUNCTIONS

makeFunEnv :: CoreProgram -> FunEnv
makeFunEnv p = M.fromList $ map (\x -> ((ident . funcName) x, x)) p

initVarEnv :: VarEnv
initVarEnv = VarEnv { anc = M.empty, dyn = M.empty, counter = "A" }

isDynExact :: Ident -> TC ()
isDynExact i = do env <- get
                  if (M.size . dyn) env == 1 && ident i `M.member` dyn env
                  then return ()
                  else case filter (\(_, t) -> t /= UnitT) (M.toList $ dyn env) of
                    [_] -> return ()
                    _  -> throwError . E.dynNotExact i $ dyn env

isDynEmpty :: TC ()
isDynEmpty = do env <- get
                if (M.null . dyn) env
                then return ()
                else case filter (\(_, t) -> t /= UnitT) (M.toList $ dyn env) of
                  [] -> return ()
                  _  -> throwError . E.dynNotEmpty $ dyn env

addDyn :: Ident -> BType -> TC ()
addDyn i t = modify $ \env -> env { dyn = M.insert (ident i) t (dyn env) }

addDyns :: Expr -> Expr -> BType -> TC ()
addDyns le e = add le
  where
    add (Var i) t = guaranteeNewUsed i e >> addDyn i t
    add (Prod e1 e2) (ProdT t1 t2) = add e1 t1 >> add e2 t2
    add _ _       = return ()

setDyn :: DynEnv -> TC ()
setDyn dynenv = do modify $ \env -> env { dyn = dynenv }
                   return ()

addAncillae :: Ident -> AType -> TC ()
addAncillae i t = modify $ \env -> env { anc = M.insert (ident i) t (anc env) }

addVar :: Ident -> Expr -> BType -> DynEnv -> TC ()
addVar i e t env =
  if not (any (\(_, t) -> t /= UnitT) (M.toList env))
  then addAncillae i (ABType t)
  else guaranteeNewUsed i e >> addDyn i t

dynLookup :: Ident -> TC (Maybe BType)
dynLookup i = do env <- get
                 return $ M.lookup (ident i) (dyn env)

funLookup :: Ident -> TC (Maybe Func)
funLookup i = do fenv <- ask
                 return $ M.lookup (ident i) fenv

ancillaeLookup :: Ident -> TC (Maybe AType)
ancillaeLookup i = do env <- get
                      return $ M.lookup (ident i) (anc env)

funArgToFun :: Ident -> FType -> TC (Func, BType)
funArgToFun i ft =
  let (unis, ft') = parseUnis ft
      (ret, fargs) = parseArgs ft'
      pnames = zip [0 .. length fargs] fargs
      fparams = map (\(pn, ft) -> (Ident (show (chr pn)), ft)) pnames
  in return (Func i unis fparams Unit, ret)
  where
    parseUnis (UnivT u t) = let (unis, t') = parseUnis t
                            in (u:unis, t')
    parseUnis t = ([], t)
    parseArgs (DynT bt1 bt2) = (bt2, [ABType bt1])
    parseArgs (BAncT bt ft') = let (ret, bts) = parseArgs ft'
                               in (ret, ABType bt:bts)
    parseArgs (FAncT _ _) = error "Failed to parse argument."

substitude :: Ident -> BType -> BType -> TC BType
substitude x t t' = return $ sub t
  where
    sub UnitT = UnitT
    sub (TVar y) | x == y = t'
    sub (TVar y) | x /= y = TVar y
    sub (ProdT t1 t2) = ProdT (sub t1) (sub t2)
    sub (SumT t1 t2) = SumT (sub t1) (sub t2)
    sub (RecT y t1) = RecT y (sub t1)
    sub t1 = error $ "not supported: " ++ show t1
