module Errors where

import CommonAst
import Core.CoreAst
import Core.CorePrettyPrinter
import qualified Data.Map as M

-- TypeChecking Errors

lookupFailed :: String
lookupFailed = "Something went wrong with lookup"

dynNotEmpty :: M.Map String BType -> String
dynNotEmpty dyn = "The following dynamic variables were not used: " ++ show dyn

dynNotExact :: Ident -> M.Map String BType -> String
dynNotExact i dyn = "The dynamic context should only include " ++ ident i
                 ++ " but included: " ++ show dyn

varNotBound :: Ident -> String
varNotBound i = "The following variable was not bound in either environment: "
             ++ ident i

paramMismatch :: String
paramMismatch = "Mismatch between number of parameters and type signature in clause"

illegalDynParam :: Func -> String
illegalDynParam f = "Function type declared for dynamic variable" ++ (ident . funcName) f

noDynamicContexts :: [String] -> String
noDynamicContexts fs = "No dynamic contexts matched. Errors include: " ++ show fs

caseTypesDontMatch :: BType -> BType -> String
caseTypesDontMatch t1 t2 = "Types in a case-expression's branches do not match: "
                        ++ show t1 ++ " contra " ++ show t2

caseNotSum :: BType -> String
caseNotSum t = "Expression cased over is not a sum-type: " ++ show t

rollNotRecursive :: BType -> String
rollNotRecursive t = "Tried to roll non-recursive type: " ++ show t

unrollNotRecursive :: BType -> String
unrollNotRecursive t = "Tried to unroll non-recursive type: " ++ show t

illegalFunctionType :: Ident -> String
illegalFunctionType i = "A variable bound to a function type may not be used here: "
                     ++ ident i

badAssignment :: Ident -> Ident -> BType -> String
badAssignment x y t = "Tried to assign something of type " ++ show t
                   ++ " to the tuple " ++ show (x, y)

newVarNotUsed :: Ident -> String
newVarNotUsed i = "Variable name introduced in let or case-expression is not used: "
               ++ ident i

functionDoesntExist :: Ident -> String
functionDoesntExist f = "Function does not exist: " ++ ident f

wrongArgType :: (Show a) => Ident -> Ident -> a -> a -> String
wrongArgType f pn t t' = "Type of argument " ++ ident pn ++ " of a call to "
                      ++ ident f ++ " is wrong. Function got: " ++ show t'
                      ++ " but expected: " ++ show t

expectedGroundType :: AType -> String
expectedGroundType t = "Expected ground type, got: " ++ show t

expectedFunctionType :: BType -> String
expectedFunctionType t = "Expected function type, got: " ++ show t

tooFewArgs :: Ident -> [Param] -> String
tooFewArgs f ps = "Not enough arguments supplied to call to: " ++ ident f
               ++ ". Parameters missing: " ++ show ps

tooManyArgs :: Ident -> [Expr] -> String
tooManyArgs f es = "Too many arguments supplied to call to: " ++ ident f
               ++ ". Arguments left over: " ++ show es

tooManyTypeArgs :: Ident -> String
tooManyTypeArgs f = "Too many type instantations for call to : " ++ ident f

tooFewTypeArgs :: Ident -> String
tooFewTypeArgs f = "Too few type instantations for call to : " ++ ident f

rollTypeMismatch :: BType -> BType -> String
rollTypeMismatch e_t sub_t = "Rolled expression was not of correct type. Type of expression: "
                          ++ show e_t ++ " contra expected type: " ++ show sub_t

unrollTypeMismatch :: BType -> BType -> String
unrollTypeMismatch t ut = "Expression was not of correct recursive type. Type of e: "
                       ++ show t ++ " vs type of sub_t: " ++ show ut

functionShadowed :: Ident -> String
functionShadowed f = "Naming of function parameter coincides with top level function: "
                  ++ show f

-- Interpretation Errors

invNotBound :: Ident -> String
invNotBound x = "Variable not bound in store after inverse interpretation: "
             ++ show x

invInterpError :: Ident -> String -> String
invInterpError f err = "Error occured during inverse interpretation of function "
                    ++ show f ++ ": " ++ err

invBadFreeVal :: Value -> Expr -> String
invBadFreeVal c e = "The free value and expression form did not match. Free value: "
                 ++ show c ++ " and expression: " ++ show e

invVarNotBound :: Ident -> String
invVarNotBound x = "Variable not bound in store during inverse evaluation: "
                ++ show x

inFunNotBound :: Ident -> String
inFunNotBound f = "Function not bound in store during interpretation: "
               ++ show f

inFMPFailed :: Value -> [Expr] -> String
inFMPFailed c lvs = "First Match Policy failed. Value produced: "
                 ++ show c ++ ". Leaves set: " ++ show lvs

inExprWrong :: Expr -> String
inExprWrong e = "Expression is of an impossible form during interpretation: "
             ++ show e
