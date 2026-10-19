module CaraML.Unverified
  ( -- * The AST mirror
    Nm
  , Mpath
  , Mexpr (..)
  , Mdecl (..)
  , Msig (..)
  , Mspec (..)
  , Expr (ECon, EList, ENum, EStr, ETuple)
    -- * Not yet exported
  , parseFile
  , parseSig
  , typecheck
  , printProgram
  ) where

import Data.Text (Text)

type Nm = Text

type Mpath = [Nm]

data Mexpr
  = MPath Mpath
  | MStruct [Mdecl]
  | MApp Mexpr Mexpr
  | MSeal Mexpr Msig
  | MErr
  deriving (Eq, Show)

data Mdecl
  = DLet Nm Expr
  | DMod Nm [(Nm, Msig)] (Maybe Msig) Mexpr
  | DSig Nm Msig
  | DImpl Nm [(Nm, Msig)] (Maybe Msig) Mexpr
  | DOpen Mpath
  | DInc Mexpr
  | DErr
  deriving (Eq, Show)

data Msig
  = SPath Mpath
  | SLit [Mspec]
  deriving (Eq, Show)

data Mspec
  = SpMod Nm Msig
  | SpInc Msig
  deriving (Eq, Show)

data Expr
  = EStr Text
  | ENum Integer
  | ETuple [Expr]
  | EList [Expr]
  | ECon Mpath [Expr]
  deriving (Eq, Show)

parseFile :: Text -> Either Text [Mdecl]
parseFile _ = Left "the parser is not implemented yet"

parseSig :: Text -> Either Text [Mspec]
parseSig _ = Left "the parser is not implemented yet"

typecheck :: [Mdecl] -> Either Text ()
typecheck _ = Left "the checker is not implemented yet"

printProgram :: [Mdecl] -> Either Text Text
printProgram _ = Left "the printer is not implemented yet"