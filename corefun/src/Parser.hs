module Parser where

import CommonAst
import Ast

import Control.Monad (void, guard)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Map as M

type Parser = Parsec String String
type ParserError = ParseError Char String

-- -- PARSER ENTRY INTERFACE -- --

parseFromFile :: FilePath -> IO (Either ParserError ExtendedProgram)
parseFromFile fname =
  do input <- readFile fname
     return (parse programParser fname input)

parseFromString :: String -> Either String ExtendedProgram
parseFromString s = case parse programParser "" s of
  Left e  -> Left (show e)
  Right p -> Right p

-- -- PARSER COMBINATORS -- --

reservedWords :: [String]
reservedWords = ["let", "in", "case", "of", "roll", "unroll", "inr", "inl",
                 "end", "type", "within", "class", "where", "instance",
                 "otherwise", "record", "do", "esac"]

lineComment :: Parser ()
lineComment = L.skipLineComment "--"

scn :: Parser ()
scn = L.space (void spaceChar) lineComment empty

sc :: Parser ()
sc = L.space (void $ oneOf " \t") lineComment empty

programParser :: Parser ExtendedProgram
programParser = scn >> pProgram <* scn <* eof

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

lexemen :: Parser a -> Parser a
lexemen = L.lexeme scn

symbol :: String -> Parser ()
symbol s = void $ L.symbol' sc s

symboln :: String -> Parser ()
symboln s = void $ L.symbol' scn s

reserved :: String -> Parser ()
reserved s = lexeme (void $ string s)

reservedn :: String -> Parser ()
reservedn s = lexemen (void $ string s)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

curlies :: Parser a -> Parser a
curlies = between (symbol "{") (symbol "}")

pIdentifier :: Parser Ident
pIdentifier = lexeme p
  where
    p = do _ <- lookAhead lowerChar
           str <- some (alphaNumChar
                    <|> char '-'
                    <|> char '_'
                    <|> char '\''
                    <?> "identifier")
           guard (str `notElem` reservedWords)
           return $ Ident str

pCapIdentifier :: Parser Ident
pCapIdentifier = lexeme p
  where
    p = do _ <- lookAhead upperChar
           str <- some alphaNumChar
           return $ Ident str

pPrimeIdentifier :: Parser Ident
pPrimeIdentifier = lexeme p
  where
    p = do _ <- lookAhead (symbol "'")
           str <- some (alphaNumChar
                   <|> char '\''
                   <?> "prime identifier")
           return $ Ident str

pProgram :: Parser ExtendedProgram
pProgram = some $ pDeclaration <* scn

pDeclaration :: Parser Declaration
pDeclaration = pTypeDef
           <|> pClassDef
           <|> pInstanceDef
           <|> pRecordDef
           <|> try pCoreFunDef
           <|> pFunDef
           <?> "declaration"

pFunDef :: Parser Declaration
pFunDef =
  do (fn, sig, rests) <- pFunSig
     fcs <- some $ pFunClause fn <* scn
     return . FuncDec $ Func fn rests sig fcs

pCoreFunDef :: Parser Declaration
pCoreFunDef =
  do idt <- pIdentifier
     unis <- try (many pPrimeIdentifier)
     params <- try (many pFunParam)
     symboln "="
     e <- pExpr
     return . CoreFuncDec $ CoreFunc idt unis params e

pFunSig :: Parser (Ident, FType, [Restriction])
pFunSig =
  do fn <- pIdentifier
     symbol "::"
     rests <- pRestrictions
     ft <- pFType
     scn
     return (fn, ft, rests)

pRestrictions :: Parser [Restriction]
pRestrictions =
     try (do rests <- (do c <-pCapIdentifier
                          a <- pPrimeIdentifier
                          return (c, a)) `sepBy1` symbol ","
             symbol "=>"
             return rests
         )
 <|> return []

pFunClause :: Ident -> Parser FuncClause
pFunClause fn =
  do reserved $ ident fn
     ps <- many pFunDefParam
     symbol "="
     cbody <- pExpr
     g <- pGuard
     return (ps, cbody, g)

pGuard :: Parser (Maybe Expr)
pGuard = try (do symbol "|"
                 e <- pExpr
                 return $ Just e
             )
     <|> try (do symbol "|"
                 reserved "otherwise"
                 return Nothing)
     <|> return Nothing

pTypeDef :: Parser Declaration
pTypeDef =
  do reserved "type"
     tn <- pCapIdentifier
     tps <- many pPrimeIdentifier
     symbol "="
     tcs <- pVariant pPrimeIdentifier `sepBy1` symbol "|"
     return $ TypeDec (DataType tn tps tcs)

pClassDef :: Parser Declaration
pClassDef =
  do reserved "class"
     name <- pCapIdentifier
     var <- pPrimeIdentifier
     reservedn "where"
     members <- some pClassMember
     return . ClassDec $ Class name var members

pClassMember :: Parser ClassMember
pClassMember =
  do funName <- pIdentifier
     symbol "=>"
     sig <- pFType
     return (funName, sig)

pInstanceDef :: Parser Declaration
pInstanceDef =
  do reserved "instance"
     name <- pCapIdentifier
     typ <- pCapIdentifier
     reservedn "where"
     members <- some pInstanceMember
     return . InstanceDec $ Instance name typ members

pInstanceMember :: Parser InstanceMember
pInstanceMember =
  do name <- pIdentifier
     params <- some pFunAppParam
     symbol "=>"
     body <- pExpr
     return $ MemberInstance name params body

pRecordDef :: Parser Declaration
pRecordDef =
  do reserved "record"
     name <- pIdentifier
     symbol "="
     members <- curlies (pRecordMember pBType `sepBy1` symbol ",")
     return . RecordDec $ Record name members

pRecordMember :: Parser a -> Parser (RecordMember a)
pRecordMember p =
  do l <- pIdentifier
     symbol "="
     typ <- p
     return (l, typ)

pFunParam :: Parser (Ident, AType)
pFunParam =
  parens $ do i <- pIdentifier
              symbol ":"
              t <- pAType
              return (i, t)

pVariant :: Parser a -> Parser (TypeCons a)
pVariant p =
  do cn <- pCapIdentifier
     cps <- many (pConsParams p)
     return $ TypeCons cn cps

pConsParams :: Parser a -> Parser (ConsParam a)
pConsParams p = do a <- p; return $ TypeVar a
            <|> do ic <- pVariant p; return $ ConsInner ic
            <|> parens (pConsParams p)

pBType :: Parser BType
pBType = try prodP
     <|> try sumP
     <|> baseP
     <|> parens pBType
     <?> "simple type"
  where
    baseP = unitP
        <|> varP
        <|> recP
        <|> consP
        -- <|> recordP
        <|> parens pBType
    prodP = do p <- baseP
               symbol "*"
               ps <- baseP `sepBy1` symbol "*"
               return $ ProdT (p:ps)
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
    -- recordP = do rn <- pIdentifier PROBLEMATIC AS IT MATCHES EXPRESSIONS
    --              return $ RcrdT rn
    varP = do tv <- pPrimeIdentifier
              return $ TVar tv
    consP = do tn <- pCapIdentifier
               tps <- many pBType -- pPrimeIdentifier
               return $ VrntT tn tps

pFType :: Parser FType
pFType = try (symbol "." >> pFType)
     <|> try uni
     <|> try ftob
     <|> try ftof
     <|> btob
     <?> "function type"
  where
    uni = do _ <- lookAhead (some pPrimeIdentifier >> symbol ".")
             u <- pPrimeIdentifier
             ft <- pFType
             return $ UnivT u ft
    ftof = do ft <- parens pFType
              symbol "->"
              ft' <- pFType
              return $ FAncT ft ft'
    ftob = do t <- pBType
              symbol "->"
              ft <- pFType
              return $ BAncT t ft
    btob = try (do t <- pBType
                   symbol "<->"
                   t' <- pBType
                   return $ DynT t (Just t'))
       <|> do t <- pBType
              return $ DynT t Nothing

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
                        ls <- pIdentifier `sepBy1` symbol ","
                        return $ VarList (l1:ls)

pFunDefParam :: Parser Expr
pFunDefParam = try pUnitExpr
           <|> try pInlExpr
           <|> try pInrExpr
           <|> try pProdExpr
           <|> try pFunDefVariant
           <|> try pVarExpr
           <|> parens pFunDefParam
           <?> "def param"

pFunDefVariant :: Parser Expr
pFunDefVariant = try (parens pVariantExpr)
             <|> (do v <- pCapIdentifier; return . Vrnt $ TypeCons v [])

pFunAppParam :: Parser Expr
pFunAppParam = try pUnitExpr
           <|> try pInlExpr
           <|> try pInrExpr
           <|> pRollExpr
           <|> try pVariantExpr
           <|> try pProdExpr
           <|> try (parens pAppExpr)
           <|> try pVarExpr
           <|> parens pFunAppParam
           <?> "app param"

pExpr :: Parser Expr
pExpr = pInlExpr
    <|> pInrExpr
    <|> pLetExpr
    <|> pCaseExpr
    <|> pRollExpr
    <|> pUnrollExpr
    <|> pVariantExpr
    <|> pRecordWithinExpr
    <|> try pUnitExpr
    <|> try pProdExpr
    <|> try pRecordDecExpr
    <|> try pAppExpr
    <|> try pInvAppExpr
    <|> try pVarExpr
    <|> parens pExpr
    <?> "expression"

pWithinExpr :: Parser WithinExpr
pWithinExpr = try pAssignExpr
          <|> try pGetExpr
          <|> try pWithinLetExpr
          <|> try (do e <- pExpr; return $ Reg e)
          <?> "within-expression"

pAccessor :: Parser (Ident, Ident)
pAccessor = do rec <- pIdentifier
               symbol "."
               lab <- pIdentifier
               return (rec, lab)

pGetExpr :: Parser WithinExpr
pGetExpr =
  do (rec, lab) <- pAccessor
     return $ Get rec lab

pAssignExpr :: Parser WithinExpr
pAssignExpr =
  do (rec, lab) <- pAccessor
     symbol "="
     e <- pWithinExpr
     return $ Assign rec lab e

pWithinLetExpr :: Parser WithinExpr
pWithinLetExpr = do reserved "let"
                    (rec, lab) <- pAccessor
                    symbol "="
                    e1 <- pWithinExpr <* scn
                    reserved "in"
                    e2 <- pWithinExpr
                    return $ WithinLet rec lab e1 e2

pUnitExpr :: Parser Expr
pUnitExpr = symbol "(" >> symbol ")" >> return Unit

pVarExpr :: Parser Expr
pVarExpr  = do i <- pIdentifier
               return $ Var i

pInlExpr :: Parser Expr
pInlExpr = do reserved "inl"
              e <- parens pExpr
              return $ Inl e

pInrExpr :: Parser Expr
pInrExpr = do reserved "inr"
              e <- parens pExpr
              return $ Inr e

pProdExpr :: Parser Expr
pProdExpr = parens $ do e1 <- pExpr
                        symbol ","
                        es <- pExpr `sepBy1` symbol ","
                        return $ Prod (e1:es)

pLetExpr :: Parser Expr
pLetExpr = do reserved "let"
              ls <- some (try reg <|> inv)
              reserved "in"
              e2 <- pExpr
              return $ LetIn ls e2
  where
    reg = do l <- pLExpr
             symbol "="
             e <- pExpr <* scn
             return (l, e)
    inv = do e <- pExpr
             symbol "="
             f <- pInvAppExpr <* scn
             return (InvExpr e, f)

pCaseExpr :: Parser Expr
pCaseExpr = do reserved "case"
               e1 <- pExpr
               reservedn "of"
               cases <- (do ls <- pExpr
                            symbol "->"
                            rs <- pExpr
                            return (ls, rs)) `sepBy` symboln ","
               scn >> reserved "esac"
               return $ CaseOf e1 cases

pAppExpr :: Parser Expr
pAppExpr = try (do f <- pIdentifier
                   ts <- some (try $ sc >> pBType)
                   es <- some (sc >> pFunAppParam)
                   return $ FunApp f ts es)
       <|> (do f <- pIdentifier
               es <- some (sc >> pFunAppParam)
               return $ FunApp f [] es)
       <?> "function application"

pInvAppExpr :: Parser Expr
pInvAppExpr = try (do f <- pIdentifier
                      symbol "!"
                      ts <- some (try $ sc >> pBType)
                      es <- some (sc >> pFunAppParam)
                      return $ InvApp f ts es)
          <|> (do f <- pIdentifier
                  symbol "!"
                  es <- some (sc >> pFunAppParam)
                  return $ InvApp f [] es)
          <?> "inverse function application"

pRollExpr :: Parser Expr
pRollExpr = do reserved "roll"
               t <- brackets pBType
               e <- pExpr
               return $ Roll t e

pUnrollExpr :: Parser Expr
pUnrollExpr = do reserved "unroll"
                 t <- brackets pBType
                 e <- pExpr
                 return $ Unroll t e

pVariantExpr :: Parser Expr
pVariantExpr = do v <- pVariant pFunDefParam
                  return $ Vrnt v

pRecordDecExpr :: Parser Expr
pRecordDecExpr =
  do name <- pIdentifier
     members <- curlies (pRecordMember pExpr `sepBy1` symbol ",")
     return $ Rcrd (Record name members)

pRecordWithinExpr :: Parser Expr
pRecordWithinExpr =
  do reserved "within"
     r <- pIdentifier
     reservedn "do"
     w <- pWithinExpr <* scn
     reserved "end"
     return $ Within r w
