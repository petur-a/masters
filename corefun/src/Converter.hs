module Converter where

import Core.CoreAst as Co
import Ast as Ex

convert :: ExtendedProgram -> IO CoreProgram
convert p = let filtered = [f | CoreFuncDec f <- p]
            in return $ map conFunc filtered

conFunc :: CoreFunc -> Co.Func
conFunc (CoreFunc f us ps e) = Co.Func f us (map conParams ps) (conExpr e)

conParams :: Ex.Param -> Co.Param
conParams (i, t) = (i, conAType t)

conAType :: Ex.AType -> Co.AType
conAType (Ex.AFType t) = Co.AFType $ conFType t
conAType (Ex.ABType t) = Co.ABType $ conBType t

conFType :: Ex.FType -> Co.FType
conFType (Ex.FAncT t1 t2) = Co.FAncT (conFType t1) (conFType t2)
conFType (Ex.BAncT t1 t2) = Co.BAncT (conBType t1) (conFType t2)
conFType (Ex.DynT t1 (Just t2)) = Co.DynT (conBType t1) (conBType t2)
conFType (Ex.UnivT u t) = Co.UnivT u $ conFType t
conFType t = error $ "CANNOT CONVERT: " ++ show t

conBType :: Ex.BType -> Co.BType
conBType Ex.UnitT = Co.UnitT
conBType (Ex.ProdT [t1, t2]) = Co.ProdT (conBType t1) (conBType t2)
conBType (Ex.SumT  t1 t2) = Co.SumT (conBType t1) (conBType t2)
conBType (Ex.TVar x) = Co.TVar x
conBType (Ex.RecT x t) = Co.RecT x $ conBType t
conBType t = error $ "CANNOT CONVERT: " ++ show t

conExpr :: Ex.Expr -> Co.Expr
conExpr Ex.Unit = Co.Unit
conExpr (Ex.Var x) = Co.Var x
conExpr (Ex.Inl e) = Co.Inl $ conExpr e
conExpr (Ex.Inr e) = Co.Inr $ conExpr e
conExpr (Ex.Prod [e1, e2]) = Co.Prod (conExpr e1) (conExpr e2)
conExpr (Ex.Roll t e) = Co.Roll (conBType t) (conExpr e)
conExpr (Ex.Unroll t e) = Co.Unroll (conBType t) (conExpr e)
conExpr (Ex.FunApp f ts es) = Co.FunApp f (map conBType ts) (map conExpr es)
conExpr (Ex.InvApp f ts es) = Co.InvApp f (map conBType ts) (map conExpr es)
conExpr (Ex.LetIn [(l, ein)] eout) = Co.LetIn (conLExpr l) (conExpr ein) (conExpr eout)
conExpr (Ex.CaseOf e [(l1, e1), (l2, e2)]) =
  Co.CaseOf (conExpr e) (conExpr l1, conExpr e1) (conExpr l2, conExpr e2) Nothing
conExpr e = error $ "CANNOT CONVERT: " ++ show e

conLExpr :: Ex.LExpr -> Co.LExpr
conLExpr (Ex.LVar x) = Co.LVar x
conLExpr (Ex.VarList [l1, l2]) = Co.VarTuple l1 l2
conLExpr l = error $ "CANNOT CONVERT: " ++ show l
