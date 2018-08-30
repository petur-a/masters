
import qualified Data.Map as M
import Data.List

-- Core
import Core.CoreAst as CoA
import qualified Core.CoreParser as CoP

-- Extended
import Ast as ExA
import qualified Parser as ExP

import Transpiler
import CommonAst
import TypeChecker (typecheck)
import Interpreter (runIn, makeFunEnv, InResult, subType, subExpr, exprToCanon, iExpr)
import Converter

import System.Environment
import System.Exit

main :: IO ()
main =
  do args <- getArgs
     case args of
       (t : filename : args') ->
         case t of
           "core" ->
            case args' of
              (f : params) ->
                do p <- parseCoreProgram filename
                   _ <- typecheckProgram p
                   case interpretFun p (Ident f) params of
                     Left e -> putStrLn $ "Run-time error: " ++ e
                     Right val -> print val
              _ -> putStrLn "Missing start function and potential parameters"
           "ext" ->
             do p <- parseExtendedProgram filename
                let p' = transpile p
                cp <- convert p'
                print cp
                _ <- typecheckProgram cp
                case args' of
                  (f : params) ->
                    case interpretFun cp (Ident f) params of
                      Left e -> putStrLn $ "Run-time error: " ++ e
                      Right val -> print val
                  [] -> do putStrLn . intercalate "\n\n" $ map show cp
                           return ()
           _ -> putStrLn "Parser mode not accepted. Try \"core\" or \"ext\""
       _ -> putStrLn $ "Wrong number of arguments.\n"
                    ++ "Usage:\n  \"rfun\" parsertype programfile startfunc startvalue+\n"
                    ++ "or to stop before interpretation:\n  \"rfun\" programfile "

typecheckProgram :: CoreProgram -> IO String
typecheckProgram p =
  case typecheck p of
        Right cons ->
          return $ "Success. The constrains generated: "
                ++ foldl (\s (cn, ct) -> s ++ "\n" ++ show cn ++ ": " ++ show ct) "" cons
        Left e   -> putStrLn e >> exitWith (ExitFailure 1)

parseCoreProgram :: String -> IO CoreProgram
parseCoreProgram filename = CoP.parseFromFile filename >>= fromParserError

parseExtendedProgram :: String -> IO ExtendedProgram
parseExtendedProgram filename = ExP.parseFromFile filename >>= fromParserError

fromParserError :: Either CoP.ParserError a -> IO a
fromParserError (Left err) = print err >> exitWith (ExitFailure 1)
fromParserError (Right a)  = return a

interpretFun :: CoreProgram -> Ident -> [String] -> InResult Value
interpretFun prog fi params =
  let fenv = makeFunEnv prog
  in case M.lookup (ident fi) fenv of
    Nothing -> Left "The attempted starting function does not exist"
    Just f@(CoA.Func _ ts ps _) ->
      if length ts + length ps /= length params
      then Left "Wrong number of arguments to starting function"
      else let e' = bindParams f params
           in case e' of
             Left s    -> Left s
             Right e'' -> runIn (iExpr e'') fenv

bindParams :: CoA.Func -> [String] -> Either String CoA.Expr
bindParams (CoA.Func _ [] [] e) [] = Right e
bindParams (CoA.Func f (t:ts) xs e) (p:ps) = case CoP.parseTypeFromParam p of
  Left _ -> Left "Failed to parse type argument"
  Right t' -> let e' = subType t' t e
              in bindParams (CoA.Func f ts xs e') ps
bindParams (CoA.Func f [] ((x, _):xs) e) (p:ps) = case CoP.parseExprFromParam p of
  Left _ -> Left "Failed to parse expression argument"
  Right x' -> let e' = subExpr (exprToCanon x') (CoA.Var x) e
              in bindParams (CoA.Func f [] xs e') ps
