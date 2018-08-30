module Core.CorePrettyPrinter where

import Core.CoreAst
import CommonAst

instance Show FType where
  show = ppFType

instance Show BType where
  show = ppBType

instance Show AType where
  show = ppAType

instance Show Func where
  show = ppFunc

instance Show Expr where
  show = ppExpr

instance Show ExitAssertion where
  show = ppExitAssertion

instance Show LExpr where
  show = ppLExpr

instance Show Value where
  show = ppValue

ppValue :: Value -> String
ppValue CanonUnit = "()"
ppValue (CanonInl v) = "inl(" ++ show v ++ ")"
ppValue (CanonInr v) = "inr(" ++ show v ++ ")"
ppValue (CanonProd v1 v2) = "(" ++ show v1 ++ ", " ++ show v2 ++ ")"
ppValue (CanonRoll t v) = "roll [" ++ show t ++ "] " ++ show v
ppValue (CanonVar x) = ident x

ppBType :: BType -> String
ppBType UnitT = "1"
ppBType (TVar i) = ident i
ppBType (UVar i) = "`" ++ ident i ++ "`"
ppBType (RecT i t) = "\\" ++ ident i ++ " . " ++ ppBType t
ppBType (SumT t t') = "(" ++ ppBType t ++ " + " ++ ppBType t' ++ ")"
ppBType (ProdT t t') = "(" ++ ppBType t ++ " * " ++ ppBType t' ++ ")"

ppFType :: FType -> String
ppFType (UnivT a t) = case t of
  UnivT _ _ -> ident a ++ " " ++ ppFType t
  _ -> ident a ++ " . " ++ ppFType t
ppFType (FAncT t1 t2) = ppFType t1 ++ " -> " ++ ppFType t2
ppFType (BAncT t1 t2) = show t1 ++ " -> " ++ ppFType t2
ppFType (DynT t1 t2) = show t1 ++ " <-> " ++ show t2

ppAType :: AType -> String
ppAType (AFType t) = show t
ppAType (ABType t) = show t

ppFunc :: Func -> String
ppFunc (Func fn as ps e) =
  let ns = ident fn
      ass = unwords $ map ident as
      pss = unwords $ map (\(p, t) -> "(" ++ ident p ++ ":" ++ show t ++ ")") ps
      es = show e
  in ns ++ " " ++ ass ++ " " ++ pss ++ " = " ++ es

ppExpr :: Expr -> String
ppExpr Unit = "()"
ppExpr (Var x) = ident x
ppExpr (Inl e) = "inl(" ++ ppExpr e ++ ")"
ppExpr (Inr e) = "inr(" ++ ppExpr e ++ ")"
ppExpr (Roll t e) = "roll [" ++ show t ++ "] " ++ ppExpr e
ppExpr (Unroll t e) = "unroll [" ++ show t ++ "] " ++ ppExpr e
ppExpr (Prod e1 e2) = "(" ++ ppExpr e1 ++ ", " ++ ppExpr e2 ++ ")"
ppExpr (LetIn x e1 e2) =
  "let " ++ show x ++ " = " ++ ppExpr e1 ++ " in " ++ ppExpr e2
ppExpr (CaseOf e1 (x, e2) (y, e3) ex) =
  let exs = case ex of
              Nothing -> ""
              Just ex' -> show ex'
  in "case " ++ ppExpr e1 ++ " of " ++ ppExpr x ++ " -> " ++ ppExpr e2 ++ ", "
                                    ++ ppExpr y ++ " -> " ++ ppExpr e3 ++ " " ++ exs
ppExpr (FunApp f ts es) =
  let fs = ident f
      tss = unwords $ map show ts
      ess = unwords $ map ppExpr es
  in fs ++ " " ++ tss ++ " " ++ ess
ppExpr (InvApp f ts es) =
  let fs = ident f
      tss = unwords $ map show ts
      ess = unwords $ map ppExpr es
  in fs ++ "! " ++ tss ++ " " ++ ess

ppExitAssertion :: ExitAssertion -> String
ppExitAssertion (Safe e) = "safe " ++ show e
ppExitAssertion Unsafe = "unsafe"

ppLExpr :: LExpr -> String
ppLExpr (LVar x) = ident x
ppLExpr (VarTuple x y) = "(" ++ ident x ++ ", " ++ ident y ++ ")"
