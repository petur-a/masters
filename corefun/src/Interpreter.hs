{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Interpreter where

import Core.CorePrettyPrinter
import Core.CoreAst
import CommonAst
import qualified Errors as E

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import Data.Maybe

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State

type InResult a = Either String a

type FunEnv = M.Map String Func

makeFunEnv :: CoreProgram -> FunEnv
makeFunEnv p = M.fromList $ map (\x -> ((ident . funcName) x, x)) p

type VarEnv = M.Map String Value

newtype I a = I { runI :: ReaderT FunEnv (Except String) a }
  deriving (Applicative, Functor, Monad, MonadReader FunEnv, MonadError String)

newtype IV a = Inv { runInv :: StateT VarEnv
                              (ReaderT FunEnv
                              (Except String)) a }
  deriving (Applicative, Functor, Monad, MonadReader FunEnv, MonadState VarEnv,
            MonadError String)

runIn :: I a -> FunEnv -> InResult a
runIn prog fenv = runExcept (runReaderT (runI prog) fenv)

runIV :: (Value -> Expr -> IV VarEnv)
      -> Value -> Expr -> VarEnv -> FunEnv -> InResult (VarEnv, VarEnv)
runIV prog c e venv fenv = runExcept (runReaderT (runStateT (runInv (prog c e)) venv) fenv)

iExpr :: Expr -> I Value
iExpr Unit = return CanonUnit
iExpr (Inl e) = do c <- iExpr e; return $ CanonInl c
iExpr (Inr e) = do c <- iExpr e; return $ CanonInr c
iExpr (Prod e1 e2) =
  do c1 <- iExpr e1
     c2 <- iExpr e2
     return $ CanonProd c1 c2
iExpr (Roll t e) =
  do c <- iExpr e
     return $ CanonRoll t c
iExpr (Unroll _ e) =
  do c <- iExpr e
     case c of
       CanonRoll _ c' -> return c'
iExpr (LetIn (LVar x) e1 e2) =
  do c <- iExpr e1
     iExpr $ subExpr c (Var x) e2
iExpr (LetIn (VarTuple x y) (Prod e1 e2) e3) =
  do c1 <- iExpr e1
     c2 <- iExpr e2
     iExpr $ subExpr c1 (Var x) $ subExpr c2 (Var y) e3
iExpr (CaseOf e (Inl x, e2) (Inr y, e3) g) =
  case g of
    Nothing ->
      do e' <- iExpr e
         case e' of
           CanonInl c -> iExpr $ subExpr c x e2
           CanonInr c -> do c3 <- iExpr $ subExpr c y e3
                            checkPLVal c3 e2
                            return c3
    Just (Safe eout) ->
      do e' <- iExpr e
         case e' of
           CanonInl c ->
             do c2 <- iExpr $ subExpr c x e2
                cout <- iExpr $ subExpr c2 (Var (Ident "out")) eout
                case cout of
                  CanonInl _ -> return c2
           CanonInr c ->
             do c3 <- iExpr $ subExpr c y e3
                cout <- iExpr $ subExpr c3 (Var (Ident "out")) eout
                case cout of
                  CanonInr _ -> return c3
    Just Unsafe ->
      do e' <- iExpr e
         case e' of
           CanonInl c -> iExpr $ subExpr c x e2
           CanonInr c -> iExpr $ subExpr c y e3
iExpr (FunApp f ts es) =
  do cs <- mapM iExpr es
     fenv <- ask
     case M.lookup (ident f) fenv of
       Just (Func _ as ps e) ->
         let fe'  = foldl (\e' (a, t) -> subType t a e') e $ zip as ts
             fe'' = foldl (\e' (c, p) -> subExpr c (Var p) e') fe' (zip cs (map fst ps))
         in iExpr fe''
       Nothing -> throwError $ E.inFunNotBound f
iExpr (InvApp f ts es) =
  do cs <- mapM iExpr es
     fenv <- ask
     case M.lookup (ident f) fenv of
      Just (Func _ as ps e) ->
        let xsn1 = map fst $ init ps
            xl = fst $ last ps
            fe'  = foldl (\e' (a, t) -> subType t a e') e $ zip as ts
            fe'' = foldl (\e' (c, p) -> subExpr c (Var p) e') fe' (zip cs xsn1)
        in case runIV invExpr (last cs) e M.empty fenv of
          Left err -> throwError $ E.invInterpError f err
          Right (s, _) ->
            case M.lookup (ident xl) s of
              Nothing -> throwError $ E.invNotBound xl
              Just c -> return c
      Nothing -> throwError $ E.inFunNotBound f
iExpr e = throwError $ E.inExprWrong e

checkPLVal :: Value -> Expr -> I ()
checkPLVal c e = let lv = leaves e
                 in case L.find (rel (canonToExpr c)) $ S.toList lv of
                   Nothing -> return ()
                   Just _  -> throwError $ E.inFMPFailed c (S.toList lv)

leaves :: Expr -> S.Set Expr
leaves Unit = S.singleton Unit
leaves e@(Var _) = S.singleton e
leaves (Inl e) = S.map Inl $ leaves e
leaves (Inr e) = S.map Inr $ leaves e
leaves (Prod e1 e2) = let es1' = leaves e1
                          es2' = leaves e2
                      in S.map (uncurry Prod) $ cartesianProduct es1' es2'
leaves (Roll t e) = S.map (Roll t) $ leaves e
leaves (Unroll t e) = S.map (Unroll t) $ leaves e
leaves (LetIn _ _ e2) = leaves e2
leaves (CaseOf _ (_, e2) (_, e3) _) = leaves e2 `S.union` leaves e3
leaves (FunApp f _ es) = let es' = map (S.toList . leaves) es
                             prods = sequence es'
                         in S.fromList $ map (FunApp f []) prods
leaves (InvApp f _ es) = let es' = map (S.toList . leaves) es
                             prods = sequence es'
                         in S.fromList $ map (InvApp f []) prods

cartesianProduct :: (Ord a, Ord b) => S.Set a -> S.Set b -> S.Set (a, b)
cartesianProduct xs ys = S.fromList $ liftA2 (,) (S.toList xs) (S.toList ys)

rel :: Expr -> Expr -> Bool
rel Unit Unit   = True
rel _ Var {}    = True
rel _ FunApp {} = True
rel _ Unroll {} = True
rel (Prod e1 e2) (Prod e1' e2') = rel e1 e1' && rel e2 e2'
rel (Inl e) (Inl e') = rel e e'
rel (Inr e) (Inr e') = rel e e'
rel (Roll t e) (Roll t' e') | t == t' = rel e e'
rel _ _ = False


invExpr :: Value -> Expr -> IV VarEnv
invExpr CanonUnit Unit = get
invExpr c (Var x) =
  do sigma <- get
     return $ M.insert (ident x) c sigma
invExpr (CanonInl c) (Inl e) = invExpr c e
invExpr (CanonInr c) (Inr e) = invExpr c e
invExpr (CanonVar x) e =
  do sigma <- get
     case M.lookup (ident x) sigma of
       Nothing -> get -- throwError $ E.invVarNotBound x
       Just c' -> invExpr c' e
invExpr (CanonProd c1 c2) (Prod e1 e2) =
  do sigma' <- invExpr c1 e1
     put sigma'
     invExpr c2 e2
invExpr (CanonRoll _ c) (Roll _ e) = invExpr c e
invExpr c (Unroll t e) = invExpr (CanonRoll t c) e
invExpr c (LetIn x e1 e2) =
  if isClosed e1
  then do p <- ask
          case runIn (iExpr e1) p of
            Left err -> error err
            Right c' -> case x of
              LVar l         -> invExpr c (subExpr c' (Var l) e2)
              VarTuple l1 l2 -> error "No such rule for products"
  else do sigma' <- invExpr c e2
          put sigma'
          case x of
            LVar l         -> invExpr (CanonVar l) e1
            VarTuple l1 l2 -> invExpr (CanonProd (CanonVar l1) (CanonVar l2)) e1
invExpr c (FunApp f ts es) =
  if all isClosed es
  then do p <- ask
          case runIn (iExpr $ InvApp f ts (init es ++ [canonToExpr c])) p of
            Left err -> error err
            Right c' -> invExpr c' (last es)
  else throwError "Expression is not closed."
invExpr c (InvApp f ts es) =
  if all isClosed es
  then do p <- ask
          case runIn (iExpr $ FunApp f ts (init es ++ [canonToExpr c])) p of
            Left err -> error err
            Right c' -> invExpr c' (last es)
  else throwError "Expression is not closed."
invExpr c (CaseOf e1 (x, e2) (y, e3) (Just (Safe eout))) =
  do fenv <- ask
     case runIn (iExpr $ subExpr c (Var (Ident "out")) eout) fenv of
       Left e -> error $ show e
       Right g -> case g of
         CanonInl CanonUnit -> do sigma' <- invExpr c e2
                                  put sigma'
                                  invExpr (CanonInl (exprToCanon x)) e1
         CanonInr CanonUnit -> do sigma' <- invExpr c e3
                                  put sigma'
                                  invExpr (CanonInr (exprToCanon y)) e1
invExpr c e = throwError $ E.invBadFreeVal c e

isClosed :: Expr -> Bool
isClosed Unit = True
isClosed (Var _) = False
isClosed (Inl e) = isClosed e
isClosed (Inr e) = isClosed e
isClosed (Roll _ e) = isClosed e
isClosed (Unroll _ e) = isClosed e
isClosed (Prod e1 e2) = isClosed e1 && isClosed e2
isClosed (LetIn _ e1 e2) = isClosed e1 && isClosed e2
isClosed (CaseOf e1 (_, e2) (_, e3) esac) = isClosed e1 && isClosed e2 && isClosed e3
isClosed (FunApp _ _ es) = all isClosed es
isClosed (InvApp _ _ es) = all isClosed es

subExpr :: Value -> Expr -> Expr -> Expr
subExpr ce (Var rep) ein = subExpr' (canonToExpr ce) ein
  where
    subExpr' _ Unit = Unit
    subExpr' c (Inl e) = Inl $ subExpr' c e
    subExpr' c (Inr e) = Inr $ subExpr' c e
    subExpr' c (Prod e1 e2) = Prod (subExpr' c e1) (subExpr' c e2)
    subExpr' c (Roll t e) = Roll t $ subExpr' c e
    subExpr' c (Unroll t e) = Unroll t $ subExpr' c e
    subExpr' c (LetIn x e1 e2) = LetIn x (subExpr' c e1) (subExpr' c e2)
    subExpr' c (CaseOf e1 (x, e2) (y, e3) esac) =
      let esac' = case esac of
                    Nothing       -> Nothing
                    Just Unsafe   -> Just Unsafe
                    Just (Safe e) -> Just . Safe $ subExpr' c e
      in CaseOf (subExpr' c e1)
                (x, subExpr' c e2)
                (y, subExpr' c e3)
                esac'
    subExpr' c (FunApp f ts es) = FunApp f ts $ map (subExpr' c) es
    subExpr' c (InvApp f ts es) = InvApp f ts $ map (subExpr' c) es
    subExpr' c (Var x) | x == rep = c
    subExpr' _ (Var x) = Var x
subExpr _ _ ein = ein

subType :: BType -> Ident -> Expr -> Expr
subType ct a e = case e of
  Roll t e1     -> Roll (subType' t) e1
  Unroll t e1   -> Unroll (subType' t) e1
  Inl e1        -> Inl (subType ct a e1)
  Inr e1        -> Inr (subType ct a e1)
  Prod e1 e2    -> Prod (subType ct a e1) (subType ct a e2)
  LetIn x e1 e2 -> LetIn x (subType ct a e1) (subType ct a e2)
  CaseOf e1 (x, e2) (y, e3) ea ->
    let ea' = case ea of
                Nothing       -> Nothing
                Just Unsafe   -> Just Unsafe
                Just (Safe e) -> Just . Safe $ subType ct a e
    in CaseOf (subType ct a e1)
              (x, subType ct a e2)
              (y, subType ct a e3)
              ea'
  e'            -> e'
  where
    subType' UnitT = UnitT
    subType' (ProdT t1 t2) = ProdT (subType' t1) (subType' t2)
    subType' (SumT t1 t2) = SumT (subType' t1) (subType' t2)
    subType' (RecT x t) = RecT x $ subType' t
    subType' (TVar x) | x == a = ct
    subType' (TVar x) = TVar x
    subType' (UVar x) = UVar x

exprToCanon :: Expr -> Value
exprToCanon Unit = CanonUnit
exprToCanon (Inl e) = CanonInl $ exprToCanon e
exprToCanon (Inr e) = CanonInr $ exprToCanon e
exprToCanon (Prod e1 e2) = CanonProd (exprToCanon e1) (exprToCanon e2)
exprToCanon (Roll t e) = CanonRoll t $ exprToCanon e
exprToCanon e = error $ "Expression is not a canonical value: " ++ show e

canonToExpr :: Value -> Expr
canonToExpr CanonUnit = Unit
canonToExpr (CanonVar x) = Var x
canonToExpr (CanonInl c) = Inl $ canonToExpr c
canonToExpr (CanonInr c) = Inr $ canonToExpr c
canonToExpr (CanonProd c1 c2) = Prod (canonToExpr c1) (canonToExpr c2)
canonToExpr (CanonRoll t c) = Roll t $ canonToExpr c
