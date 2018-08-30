module TransErrors where

import Ast
import CommonAst

-- Transpiling Errors

classNotDefined :: Ident -> String
classNotDefined c = "Tried to write an instance for a class which has not been defined: "
                 ++ show c

classNoSuchMember mb c = "Attempted to derive a function " ++ show mb ++ " for the class \""
                      ++ show (className c) ++ "\". Possible members are: "
                      ++ show (classMembers c)

contextClassNotDefined :: Ident -> Ident -> String
contextClassNotDefined fn c = "Class " ++ show c ++ " in context of function "
                           ++ show fn ++ " does not exist."

invalidOverloads :: [BType] -> String
invalidOverloads as = "The reference implementation only allows overloading of variants "
                   ++ "which are simple. Attempted to overload: " ++ show as

noDefaultGuard :: Ident -> String
noDefaultGuard f = "The last guard for a clause was not a default guard, which "
                ++ "is ill-defiled, for the function " ++ show f

namesNotInvariant :: (Show a) => [a] -> String
namesNotInvariant ps = "Names for invariant parameters are not equal: " ++ show ps

clauseExprIllFormed :: BType -> String
clauseExprIllFormed t = "Type of a top-level expression is neither a sum or variant: "
                     ++ show t

-- onlySimpleConstructors :: [BType] -> String
onlySimpleConstructors bts = "A recursive variant constructor parameter may only be simple in"
                         ++ "the reference implementation (meaning one or zero parameters). "
                         ++ "Got: " ++ show bts

onlyRecursiveInnerVariants v = "An inner variant may currently only be the same as "
                            ++ "the one being defined (recursive), got: " ++ show v

variantCaseMissing :: Ident -> String
variantCaseMissing v = "The variant constructor " ++ show v ++ " is missing "
                    ++ " from a case-expression"

variantConstructorUnknown :: Ident -> String
variantConstructorUnknown vc = "Constructor not defined for any variant: " ++ show vc

variantNotDefined :: Ident -> String
variantNotDefined v = "Variant type not defined: " ++ show v

-- "Impossible" error messages

guardForNoClauses :: String
guardForNoClauses = "Should not happen: Tried to expand a guard with zero clauses., "
                 ++ "which is non-sensical."

guardOmitted :: String
guardOmitted = "Should not happen due to reordering: An intermediate clause "
            ++ "was missing a guard."

caseNoBranches :: String
caseNoBranches = "Should not happen: A case up for translation has no branches."

caseOneBranch :: String
caseOneBranch = "Should not happen: A case up for translation only has one branch."

constructorWrong :: String
constructorWrong = "Should not happen: Trying to translate a constructor which "
                ++ "does not exist for this variant."
