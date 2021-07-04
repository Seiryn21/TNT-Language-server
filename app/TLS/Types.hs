{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DuplicateRecordFields#-}

module TLS.Types where

import           GHC.Generics
import           Data.Aeson
import qualified Data.Map           as Map
import qualified Data.Text          as T
import qualified Language.LSP.Types as LSP

data Var = A
         | B
         | C
         | D
         | E
         | Prime Var
         deriving (Eq)

data Term = Zero
          | Succ Term
          | Var Var
          | Add Term Term
          | Mul Term Term
          deriving (Eq)

data Formula = Eq Term Term
             | Not Formula
             | And Formula Formula
             | Or Formula Formula
             | Implie Formula Formula
             | Forall Var Formula
             | Exist Var Formula
             | Error T.Text
             deriving (Eq)

instance Show Var where
  show A = "a"
  show B = "b"
  show C = "c"
  show D = "d"
  show E = "e"
  show (Prime v) = show v ++ "'"

instance Show Term where
  show Zero = "0"
  show (Succ t) = "S" ++ show t
  show (Var v) = show v
  show (Add t1 t2) = "(" ++ show t1 ++ "+" ++ show t2 ++ ")"
  show (Mul t1 t2) = "(" ++ show t1 ++ "*" ++ show t2 ++ ")"

instance Show Formula where
  show (Eq t1 t2) = show t1 ++ "=" ++ show t2
  show (Not f) = "~" ++ show f
  show (And f1 f2) = "<" ++ show f1 ++ "&" ++ show f2   ++ ">"
  show (Or f1 f2) = "<" ++ show f1 ++ "|" ++ show f2 ++ ">"
  show (Implie f1 f2) = "<" ++ show f1 ++ "⊂" ++ show f2 ++ ">"
  show (Forall v f) = "∀" ++ show v ++ ":" ++ show f
  show (Exist v f) = "∃" ++ show v ++ ":" ++ show f

type Lines = [(Int, Formula)]

data Scope = Scope (Map.Map Identifier (Maybe Formula)) (Maybe Scope) Int Int Lines

type Instr = (Scope -> Scope)

type InstrBlock = (Maybe Instr, LSP.Range, LSP.Range)

type Identifier = String

data Theorem = Theorem LSP.Range LSP.Range Identifier Formula [InstrBlock]

instance Show Theorem where
    show (Theorem _ _ id f _ ) = show id ++ " " ++ show f
data Line = Line { range :: Maybe LSP.Range
                 , display :: T.Text
                 , empty :: Bool
                 } deriving (Generic, ToJSON, Show)

data ComputedTheorem = ComputedTheorem { range :: Maybe LSP.Range
                                       , lines :: Maybe [Line]
                                       } deriving (Generic, ToJSON, Show)

type ParsedFile = [ComputedTheorem]

instrs :: [String]
instrs = [ "axiom"
         , "theorem"
         , "openFantasy"
         , "closeFantasy"
         , "symmetry"
         , "transitivity"
         , "addSucc"
         , "removeSucc"
         , "join"
         , "separe"
         , "detach"
         , "contrapose"
         , "specialize"
         , "generalize"
         , "existence"
         , "recurence"
         , "addDoubleNeg"
         , "removeDoubleNeg"
         , "notOrToAndNot"
         , "andNotToNotOr"
         ]