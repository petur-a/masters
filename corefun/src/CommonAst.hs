module CommonAst where

newtype Ident = Ident { ident :: String }
              deriving (Eq, Ord)

instance Show Ident where
  show i = "\"" ++ ident i ++ "\""
