module FirstMatch where

import qualified Data.Set as S

import Core.CoreAst
import Interpreter

firstMatch :: CoreProgram -> CoreProgram
firstMatch = map (\f -> f { funcBody = analysis $ funcBody f } )

analysis :: Expr -> Expr
analysis (Inl e) = analysis e
analysis (Inr e) = analysis e
analysis (LetIn l e1 e2) = LetIn l e1 $ analysis e2
analysis (Roll t e) = Roll t $ analysis e
analysis (Unroll t e) = Unroll t $ analysis e
analysis (CaseOf e1 (x, e2) (y, e3) g) =
  let g'' = case g of
             Nothing -> tryAddAssertion e2 e3
             g' -> g'
  in CaseOf e1 (x, analysis e2) (y, analysis e3) g''
analysis e = e

tryAddAssertion :: Expr -> Expr -> Maybe ExitAssertion
tryAddAssertion e1 e2 =
  let ls1 = leaves e1
      ls2 = leaves e2
      cart = cartesianProduct ls1 ls2
      inter = S.filter (uncurry rel) cart
  in if null inter
     then Just Unsafe
     else Nothing
