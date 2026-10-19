-- | The compiler's interface to the verified compiler internals: names, errors,
-- programs, data files and the checker. The rest of the compiler is written
-- against this module only.
module CaraML.Language
  ( -- * Names
    Nm
  , Mpath
  , isModuleName
    -- * Lexical syntax
  , keywords
  , isIdentChar
    -- * Errors
  , Span (..)
  , Err (..)
  , failure
  , inFile
  , renderErr
    -- * Programs
  , Module
  , Sig
  , parseModule
  , parseSig
  , submodule
  , moduleRefs
  , sigRefs
  , boundNames
  , bindsValue
  , typecheck
  , printModule
    -- * Data files
  , Value (..)
  , parseData
  ) where

import Data.Char (isAlphaNum, isUpper)
import Data.Set (Set)
import Data.Text (Text)

import qualified Data.Set as Set
import qualified Data.Text as T

import CaraML.Unverified (Mdecl(..), Mexpr(..), Mspec(..), Msig(..), Expr(..), Mpath, Nm)

import qualified CaraML.Unverified as CaraML

-- * Names

-- | an upper-case identifier
isModuleName :: Text -> Bool
isModuleName t = case T.uncons t of
  Just (c, rest) -> isUpper c && T.all isIdentChar rest
  Nothing -> False

-- * Lexical syntax

keywords :: [Text]
keywords =
  [ "if", "else", "match", "handle", "handler", "mask", "return", "finally", "let", "fn", "as"
  , "type", "module", "signature", "implicit", "instance", "open", "include", "extern", "effect"
  , "protocol", "infix", "infixl", "infixr"
  ]

-- | a character after the first of an identifier
isIdentChar :: Char -> Bool
isIdentChar x = isAlphaNum x || x == '_' || x == '\''

-- * Errors

-- | a stretch of one line: line and column from 1, length in characters
data Span = Span
  { line :: Int
  , col  :: Int
  , len  :: Int
  } deriving (Eq, Ord, Show)

data Err = Err
  { file :: Maybe FilePath
  , span :: Maybe Span
  , msg  :: Text
  } deriving (Eq, Show)

-- | an error with neither file nor position
failure :: Text -> Err
failure = Err Nothing Nothing

-- | attribute an error without a file to @path@
inFile :: FilePath -> Either Err a -> Either Err a
inFile path = either (\e -> Left e { file = maybe (Just path) Just e.file }) Right

renderErr :: Err -> Text
renderErr (Err f p m) = T.concat [file, pos, m]
 where
  file = maybe "" (\x -> T.pack x <> ":") f
  pos = maybe sep (\sp -> T.pack (show sp.line) <> ":" <> T.pack (show sp.col) <> ": ") p
  sep | f == Nothing = ""
      | otherwise    = " "

-- | a stand-in's or the export's failure
lift :: Either Text a -> Either Err a
lift = either (Left . failure) Right

-- * Programs

-- | the declarations of a structure; '<>' sequences them
newtype Module = Module [Mdecl]
  deriving (Eq, Show)

instance Semigroup Module where
  Module a <> Module b = Module (a ++ b)

instance Monoid Module where
  mempty = Module []

-- | the specifications of a literal signature
newtype Sig = Sig [Mspec]
  deriving (Eq, Show)

parseModule :: Text -> Either Err Module
parseModule src = Module <$> lift (CaraML.parseFile src)

parseSig :: Text -> Either Err Sig
parseSig src = Sig <$> lift (CaraML.parseSig src)

-- | @module nm : sig = { body }@
submodule :: Nm -> Maybe Sig -> Module -> Module
submodule nm sig (Module ds) = Module [DMod nm [] ((\(Sig s) -> SLit s) <$> sig) (MStruct ds)]

-- | the module paths a module mentions
moduleRefs :: Module -> Set Mpath
moduleRefs (Module ds) = declsRefs ds

declsRefs :: [Mdecl] -> Set Mpath
declsRefs = Set.unions . map declRefs
 where
  declRefs d = case d of
    DLet _ e -> exprRefs e
    DMod _ ps s m -> paramRefs ps `Set.union` maybe Set.empty msigRefs s `Set.union` mexprRefs m
    DSig _ s -> msigRefs s
    DImpl _ ps s m -> paramRefs ps `Set.union` maybe Set.empty msigRefs s `Set.union` mexprRefs m
    DOpen p -> Set.singleton p
    DInc m -> mexprRefs m
    DErr -> Set.empty
  paramRefs = Set.unions . map (msigRefs . snd)
  exprRefs e = case e of
    ECon p args -> Set.insert p (Set.unions (map exprRefs args))
    ETuple es -> Set.unions (map exprRefs es)
    EList es -> Set.unions (map exprRefs es)
    _ -> Set.empty
  mexprRefs m = case m of
    MPath p -> Set.singleton p
    MStruct ds' -> declsRefs ds'
    MApp f x -> mexprRefs f `Set.union` mexprRefs x
    MSeal x s -> mexprRefs x `Set.union` msigRefs s
    MErr -> Set.empty

-- | the module paths a signature mentions
sigRefs :: Sig -> Set Mpath
sigRefs (Sig specs) = msigRefs (SLit specs)

msigRefs :: Msig -> Set Mpath
msigRefs (SPath p) = Set.singleton p
msigRefs (SLit specs) = Set.unions (map specRefs specs)
 where
  specRefs (SpMod _ s) = msigRefs s
  specRefs (SpInc s) = msigRefs s

-- | the names the top level binds
boundNames :: Module -> Set Nm
boundNames (Module ds) = Set.fromList (concatMap bound ds)
 where
  bound = \case
    DLet x _ -> [x]
    DMod x _ _ _ -> [x]
    DSig x _ -> [x]
    DImpl x _ _ _ -> [x]
    _ -> []

-- | whether the top level binds the value @nm@
bindsValue :: Nm -> Module -> Bool
bindsValue nm (Module ds) = any binds ds
 where
  binds = \case
    DLet x _ -> x == nm
    _ -> False

typecheck :: Module -> Either Err ()
typecheck (Module ds) = lift (CaraML.typecheck ds)

printModule :: Module -> Either Err Text
printModule (Module ds) = lift (CaraML.printProgram ds)

-- * Data files

-- | the data a manifest or lock file is made of
data Value
  = VStr Text
  | VNum Integer
  | VTuple [Value]
  | VList [Value]
  | VCon Mpath [Value]
  deriving (Eq, Show)

-- | a file of data bindings @x = v@, in order
parseData :: Text -> Either Err [(Nm, Value)]
parseData src = parseModule src >>= \(Module ds) -> mapM binding ds
 where
  binding = \case
    DLet x e -> Right (x, value e)
    _ -> Left (failure "only data bindings `x = data` are allowed")
  value = \case
    EStr s -> VStr s
    ENum n -> VNum n
    ETuple es -> VTuple (map value es)
    EList es -> VList (map value es)
    ECon p es -> VCon p (map value es)
