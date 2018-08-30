module Ast where

import CommonAst

-- Type Grammar stuff

data BType = UnitT
           | ProdT [BType]
           | TVar  Ident
           | UVar  Ident
           | SumT  BType BType
           | RecT  Ident BType
           | VrntT Ident [BType]
           | RcrdT Ident
           deriving (Show, Eq, Ord)

data FType = UnivT Ident FType
           | FAncT FType FType
           | BAncT BType FType
           | DynT  BType (Maybe BType)
           deriving (Eq, Show)

data AType = AFType FType
           | ABType BType
           deriving (Eq, Show)

-- Datatype Declaration Grammar Stuff

data DataType = DataType Ident [Ident] [TypeCons Ident]
              deriving (Eq, Show)

data TypeCons a = TypeCons { consName   :: Ident
                           , consParams :: [ConsParam a] }
                deriving (Eq, Show, Ord)

data ConsParam a = TypeVar a
                 | ConsInner (TypeCons a)
                 deriving (Eq, Show, Ord)

-- Function Grammar stuff

type ExtendedProgram = [Declaration]

data Declaration = TypeDec     DataType
                 | FuncDec     Func
                 | CoreFuncDec CoreFunc
                 | ClassDec    Class
                 | InstanceDec Instance
                 | RecordDec   (Record BType)
                 deriving (Eq, Show)

-- Function Declaration

data Func = Func { funcName    :: Ident
                 , classRest   :: [Restriction]
                 , funcSig     :: FType
                 , funcClauses :: [FuncClause] }
          deriving (Eq, Show)

type Restriction = (Ident, Ident) -- Type Class Name; Restricted Type Variable

type FuncClause = ([Expr], Expr, Maybe Expr) -- Parameters; Body; Guard

data CoreFunc = CoreFunc { coreFuncName   :: Ident
                         , coreFuncUnis   :: [Ident]
                         , coreFuncParams :: [Param]
                         , coreFuncBody   :: Expr }
          deriving (Eq, Show)

type Param = (Ident, AType)

-- Class Declarations

type ClassMember = (Ident, FType)

data Class = Class { className :: Ident
                   , classVar :: Ident
                   , classMembers :: [ClassMember] }
                   deriving (Eq, Show)

-- Instance Declarations

data InstanceMember = MemberInstance { memberName :: Ident
                                     , memberParams :: [Expr]
                                     , memberBody :: Expr }
                                     deriving (Show, Eq, Ord)

data Instance = Instance { classInstance :: Ident
                         , instanceType :: Ident
                         , memberInstances :: [InstanceMember] }
                         deriving (Show, Eq, Ord)

-- Record Declarations

type RecordMember a = (Ident, a)

data Record a = Record { recordName :: Ident
                       , recordMembers :: [RecordMember a] }
                       deriving (Eq, Show, Ord)

-- Expression Grammar Stuff

data Expr = Unit
          | Vrnt   (TypeCons Expr)
          | Rcrd   (Record Expr)
          | Within Ident WithinExpr
          | Inl    Expr
          | Inr    Expr
          | Prod   [Expr]
          | LetIn  [(LExpr, Expr)] Expr
          | CaseOf Expr [(Expr, Expr)]
          | FunApp Ident [BType] [Expr]
          | InvApp Ident [BType] [Expr]
          | Roll   BType Expr
          | Unroll BType Expr
          | Var    Ident
          deriving (Eq, Show, Ord)

data WithinExpr = Reg Expr
                | Get Ident Ident
                | Assign Ident Ident WithinExpr
                | WithinLet Ident Ident WithinExpr WithinExpr
                deriving (Eq, Show, Ord)

data LExpr = LVar     Ident
           | VarTuple Ident Ident
           | VarList [Ident]
           | InvExpr Expr
           deriving (Eq, Show, Ord)
