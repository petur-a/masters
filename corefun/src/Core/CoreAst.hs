module Core.CoreAst where

import CommonAst
-- import Core.CorePrettyPrinter (prettyPrint)

-- Type Grammar stuff

data BType = UnitT
           | ProdT BType BType
           | SumT  BType BType
           | RecT  Ident BType
           | TVar  Ident
           | UVar  Ident
           deriving (Ord)

data FType = FAncT FType FType
           | BAncT BType FType
           | DynT  BType BType
           | UnivT Ident FType
           deriving (Eq)

data AType = AFType FType
           | ABType BType
           deriving (Eq)

-- Function Grammar stuff

type CoreProgram = [Func]

data Func = Func { funcName   :: Ident
                 , funcUnis   :: [Ident]
                 , funcParams :: [Param]
                 , funcBody   :: Expr }
          deriving (Eq)

type Param = (Ident, AType)

-- Expression Grammar stuff

data Expr = Unit
          | Var Ident
          | Inl    Expr
          | Inr    Expr
          | Prod   Expr Expr
          | LetIn  LExpr Expr Expr
          | InvLet Expr Expr Expr
          | CaseOf Expr (Expr, Expr) (Expr, Expr) (Maybe ExitAssertion)
          | FunApp Ident [BType] [Expr]
          | InvApp Ident [BType] [Expr]
          | Roll   BType Expr
          | Unroll BType Expr
          deriving (Eq, Ord)

data ExitAssertion = Safe Expr
                   | Unsafe
          deriving (Eq, Ord)

data LExpr = LVar     Ident
           | VarTuple Ident Ident
           deriving (Eq, Ord)

-- INSTANCES

instance Eq BType where
  (==) t1 t2 = realignRecVars ['a'..] t1 `unifyTypes` realignRecVars ['a'..] t2

unifyTypes :: BType -> BType -> Bool
unifyTypes UnitT UnitT = True
unifyTypes (TVar i) (TVar i') | i == i' = True
unifyTypes (TVar i) (TVar i') = False
unifyTypes (UVar _) _ = True
unifyTypes _ (UVar _) = True
unifyTypes (ProdT t1 t1') (ProdT t2 t2') = unifyTypes t1 t2 && unifyTypes t1' t2'
unifyTypes (SumT t1 t1') (SumT t2 t2') = unifyTypes t1 t2 && unifyTypes t1' t2'
unifyTypes (RecT i t) (RecT i' t') = ident i == ident i' && unifyTypes t t'
unifyTypes _ _ = False

realignRecVars :: String -> BType -> BType
realignRecVars _ UnitT = UnitT
realignRecVars _ (TVar a) = TVar a
realignRecVars _ (UVar a) = UVar a
realignRecVars rs (ProdT t1 t2) = ProdT (realignRecVars rs t1) (realignRecVars rs t2)
realignRecVars rs (SumT t1 t2) = SumT (realignRecVars rs t1) (realignRecVars rs t2)
realignRecVars (r:rs) (RecT a t) =
  let t' = realignRecVars rs t
      rv = Ident $ "--" ++ [r]
  in RecT rv $ tvSub a (TVar rv) t'

tvSub tv newT UnitT = UnitT
tvSub tv newT (TVar a) | tv == a = newT
tvSub tv newT (TVar a) = TVar a
tvSub tv newT (ProdT t1 t2) = SumT (tvSub tv newT t1) (tvSub tv newT t2)
tvSub tv newT (SumT t1 t2) = SumT (tvSub tv newT t1) (tvSub tv newT t2)
tvSub tv newT (RecT a t) = RecT a $ tvSub tv newT t

-- Canonical Value Datatypes

data Value = CanonUnit
           | CanonInl Value
           | CanonInr Value
           | CanonProd Value Value
           | CanonRoll BType Value
           | CanonVar Ident
           deriving (Eq)
