module Core.CoreParser where

import CommonAst
import Core.CoreAst

import Control.Monad (void, guard)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Map as M

type Parser = Parsec String String
type ParserError = ParseError Char String

-- -- PARSER ENTRY INTERFACE -- --

parseFromFile :: FilePath -> IO (Either ParserError CoreProgram)
parseFromFile fname =
  do input <- readFile fname
     return (parse programParser fname input)

parseFromString :: String -> Either String CoreProgram
parseFromString s = case parse programParser "" s of
  Left e  -> Left (show e)
  Right p -> Right p

parseExprFromParam :: String -> Either ParserError Expr
parseExprFromParam = parse pExpr ""

parseTypeFromParam :: String -> Either ParserError BType
parseTypeFromParam = parse pBType ""

-- -- PARSER COMBINATORS -- --

reservedWords :: [String]
reservedWords = ["let", "in", "case", "of", "roll", "unroll", "inr", "inl",
                 "end", "safe", "unsafe"]

lineComment :: Parser ()
lineComment = L.skipLineComment "--"

scn :: Parser ()
scn = L.space (void spaceChar) lineComment empty

sc :: Parser ()
sc = L.space (void $ oneOf " \t") lineComment empty

programParser :: Parser CoreProgram
programParser = pProgram <* scn <* eof

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser ()
symbol s = void $ L.symbol' sc s

reserved :: String -> Parser ()
reserved s = lexeme (void $ string s)

lexemen :: Parser a -> Parser a
lexemen = L.lexeme scn

symboln :: String -> Parser ()
symboln s = void $ L.symbol' scn s

reservedn :: String -> Parser ()
reservedn s = lexemen (void $ string s)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

pIdentifier :: Parser Ident
pIdentifier = lexeme p
  where
    p = do
      _ <- lookAhead lowerChar
      str <- some (alphaNumChar
               <|> char '-'
               <|> char '_'
               <|> char '\''
               <?> "identifier")
      guard (str `notElem` reservedWords)
      return $ Ident str

pPrimeIdentifier :: Parser Ident
pPrimeIdentifier = lexeme p
  where
    p = do
      lookAhead (symbol "'")
      str <- some (alphaNumChar
               <|> char '\''
               <?> "prime identifier")
      return $ Ident str

pProgram :: Parser CoreProgram
pProgram = some $ pFunDef <* scn

pFunDef :: Parser Func
pFunDef =
  do idt <- pIdentifier
     unis <- try (many pPrimeIdentifier)
     params <- try (some pFunParam)
     symboln "="
     e <- pExpr
     return $ Func idt unis params e

pFunParam :: Parser (Ident, AType)
pFunParam =
  parens $ do i <- pIdentifier
              symbol ":"
              t <- pAType
              return (i, t)

pBType :: Parser BType
pBType = try prodP
     <|> try sumP
     <|> baseP
     <|> parens pBType
     <?> "simple type"
  where
    baseP = try unitP
        <|> try varP
        <|> try recP
        <|> parens pBType
    prodP = do p1 <- baseP
               symbol "*"
               p2 <- pBType
               return $ ProdT p1 p2
    unitP = do symbol "1"
               return UnitT
    sumP = do p1 <- baseP
              symbol "+"
              p2 <- pBType
              return $ SumT p1 p2
    recP = do symbol "\\"
              i <- pPrimeIdentifier
              symbol "."
              t <- pBType
              return $ RecT i t
    varP = do tv <- pPrimeIdentifier
              return $ TVar tv

pFType :: Parser FType
pFType = try ftof
     <|> try ftob
     <|> try btob
  where
    ftof = do ft <- parens pFType
              symbol "->"
              ft' <- pFType
              return $ FAncT ft ft'
    ftob = do t <- pBType
              symbol "->"
              ft <- pFType
              return $ BAncT t ft
    btob = do t <- pBType
              symbol "<->"
              t' <- pBType
              return $ DynT t t'

pAType :: Parser AType
pAType = (do t <- try pBType; return $ ABType t)
     <|> (do t <- try (parens pFType); return $ AFType t)
     <?> "parameter type"

pLExpr :: Parser LExpr
pLExpr = iden
     <|> tuple
     <?> "left expression"
  where
    iden = do i <- pIdentifier
              return $ LVar i
    tuple = parens $ do l1 <- pIdentifier
                        symbol ","
                        l2 <- pIdentifier
                        return $ VarTuple l1 l2

pExpr :: Parser Expr
pExpr = try unit
    <|> try inl
    <|> try inr
    <|> try tuple
    <|> try letin
    <|> try letinv
    <|> try caseof
    <|> try app
    <|> try invapp
    <|> try roll
    <|> try unroll
    <|> try var
    <?> "expression"
  where
    pParam = try unit
         <|> try inl
         <|> try inr
         <|> try tuple
         <|> try var
         <?> "param"
    unit = symbol "(" >> symbol ")" >> return Unit
    var = do i <- pIdentifier
             return $ Var i
    inl = do reserved "inl"
             e <- parens pExpr
             return $ Inl e
    inr = do reserved "inr"
             e <- parens pExpr
             return $ Inr e
    tuple = parens $ do e1 <- pExpr
                        symbol ","
                        e2 <- pExpr
                        return $ Prod e1 e2
    letin = do reserved "let"
               l <- pLExpr
               symbol "="
               e1 <- pExpr <* scn
               reserved "in"
               e2 <- pExpr
               return $ LetIn l e1 e2
    letinv = do reserved "let"
                e <- pExpr
                symbol "="
                e1 <- invapp <* scn
                reserved "in"
                e2 <- pExpr
                return $ InvLet e e1 e2
    caseof = do reserved "case"
                e1 <- pExpr
                reservedn "of"
                x <- inl
                symbol "=>"
                e2 <- pExpr
                symboln ","
                y <- inr
                symbol "=>"
                e3 <- pExpr
                ex <- pExitAss
                return $ CaseOf e1 (x, e2) (y, e3) ex
    app = try (do f <- pIdentifier
                  ts <- some (sc >> pBType)
                  es <- many (try $ sc >> pParam)
                  return $ FunApp f ts es)
      <|> try (do f <- pIdentifier
                  ts <- many (try $ sc >> pBType)
                  es <- some (sc >> pParam)
                  return $ FunApp f ts es)
    invapp = try (do f <- pIdentifier
                     symbol "!"
                     ts <- some (sc >> pBType)
                     es <- many (try $ sc >> pParam)
                     return $ InvApp f ts es)
         <|> try (do f <- pIdentifier
                     symbol "!"
                     ts <- many (try $ sc >> pBType)
                     es <- some (sc >> pParam)
                     return $ InvApp f ts es)
    roll = do reserved "roll"
              t <- brackets pBType
              e <- pExpr
              return $ Roll t e
    unroll = do reserved "unroll"
                t <- brackets pBType
                e <- pExpr
                return $ Unroll t e

pExitAss :: Parser (Maybe ExitAssertion)
pExitAss = return Nothing
