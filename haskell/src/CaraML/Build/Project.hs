-- | Manifests, resolution, the lock file and the whole program. Resolution is
-- minimum version selection (Gibb et al., /Package Managers à la Carte/, 2026, §3)
module CaraML.Build.Project
  ( -- * Manifests
    Name
  , Version (..)
  , parseVersion
  , renderVersion
  , Source (..)
  , Manifest (..)
  , readManifest
  , manifestSig
    -- * The index and resolution
  , Origin (..)
  , Candidate (..)
  , Index (..)
  , buildIndex
  , Package (..)
  , resolve
    -- * The lock file
  , Locked (..)
  , renderLock
  , readLock
    -- * Modules by directory and the whole program
  , Tree (..)
  , PkgSrc (..)
  , treeHeads
  , orderSiblings
  , treeDecl
  , flatten
  , dependencyCheck
  ) where

import Data.Map.Strict (Map)
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Text (Text)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T

import CaraML.Language

-- * Manifests

type Name = Text

-- | @major.minor.patch@
newtype Version = Version (Int, Int, Int)
  deriving (Eq, Ord, Show)

parseVersion :: Text -> Either Text Version
parseVersion t = case T.splitOn "." t of
  [a, b, c] | Just x <- num a, Just y <- num b, Just z <- num c -> Right (Version (x, y, z))
  _ -> Left ("not a version `major.minor.patch`: " <> T.pack (show t))
 where
  num s | not (T.null s), T.all (`elem` ("0123456789" :: String)) s, T.length s < 10 = Just (read (T.unpack s))
        | otherwise = Nothing

renderVersion :: Version -> Text
renderVersion (Version (a, b, c)) = T.intercalate "." (map (T.pack . show) [a, b, c])

-- | where the index is built from
data Source
  = Git Text        -- ^ a repository; its tags @v<version>@ are the versions
  | Dir FilePath    -- ^ a directory of packages, relative to the manifest
  deriving (Eq, Ord, Show)

data Manifest = Manifest
  { name :: Name
  , version :: Version
  , dependencies :: [(Name, Version)]    -- ^ name and lower bound
  , sources :: [Source]
  , library :: Maybe Nm                   -- ^ the root module exported to dependents
  , executables :: [(Text, Nm)]           -- ^ binary name and root module
  } deriving (Eq, Show)

manifestSig :: Text
manifestSig = T.unlines
  [ "signature PACKAGE ="
  , "  type source = Git string | Dir string"
  , "  name : string"
  , "  version : string"
  , "  dependencies : list (string, string)"
  , "  sources : list source"
  , "  library : option string"
  , "  executables : list (string, string)" ]

-- | check a manifest against @PACKAGE@
readManifest :: [(Nm, Value)] -> Either Err Manifest
readManifest fields = do
  let names = map fst fields
  mapM_ (\n -> if length (filter (== n) names) > 1 then bad ("field bound twice: " <> n) else Right ()) names
  mapM_ (\n -> if n `elem` required then Right () else bad ("not a field of PACKAGE: " <> n)) names
  mapM_ (\n -> if n `elem` names then Right () else bad ("missing field: " <> n)) required
  let get n = maybe (bad ("missing field: " <> n)) Right (lookup n fields)
  name <- get "name" >>= str "name"
  _ <- if validName name then Right () else bad ("not a package name: " <> T.pack (show name))
  version <- get "version" >>= str "version" >>= either bad Right . parseVersion
  deps <- get "dependencies" >>= list "dependencies" >>= mapM dep
  sources <- get "sources" >>= list "sources" >>= mapM source
  library <- get "library" >>= option "library" >>= traverse (\e -> str "library" e >>= modName)
  exes <- get "executables" >>= list "executables" >>= mapM exe
  pure (Manifest name version deps sources library exes)
 where
  required = ["name", "version", "dependencies", "sources", "library", "executables"]
  bad m = Left (failure ("manifest: " <> m))
  str _ (VStr s) = Right s
  str f _ = bad (f <> ": expected a string")
  list _ (VList es) = Right es
  list f _ = bad (f <> ": expected a list")
  option _ (VCon ["None"] []) = Right Nothing
  option _ (VCon ["Some"] [e]) = Right (Just e)
  option f _ = bad (f <> ": expected `None` or `Some x`")
  dep (VTuple [VStr n, VStr v]) = do
    _ <- if validName n then Right () else bad ("dependencies: not a package name: " <> T.pack (show n))
    (,) n <$> either bad Right (parseVersion v)
  dep _ = bad "dependencies: expected `(name, lower bound)` pairs of strings"
  source (VCon ["Git"] [VStr u]) = Right (Git u)
  source (VCon ["Dir"] [VStr p]) = Right (Dir (T.unpack p))
  source _ = bad "sources: expected `Git url` or `Dir path`"
  modName s = if isModuleName s then Right s else bad ("not a module name: " <> T.pack (show s))
  exe (VTuple [VStr b, VStr m]) = (,) b <$> modName m
  exe _ = bad "executables: expected `(binary, root module)` pairs of strings"
  validName n = not (T.null n) && T.all (\c -> c `elem` ("abcdefghijklmnopqrstuvwxyz0123456789-_" :: String)) n

-- * The index and resolution

-- | where a package's tree is
data Origin
  = OriginDir FilePath
  | OriginGit Text Text Text    -- ^ url, commit, subdirectory
  deriving (Eq, Ord, Show)

data Candidate = Candidate
  { source :: Text          -- ^ the source providing it
  , manifest :: Manifest
  , origin :: Origin
  } deriving (Eq, Show)

newtype Index = Index (Map Name (Map Version Candidate))
  deriving (Eq, Show)

-- | a name provided by two sources is an error
buildIndex :: [Candidate] -> Either Err Index
buildIndex cs = Index <$> Map.traverseWithKey perName (Map.fromListWith (++) [(c.manifest.name, [c]) | c <- cs])
 where
  perName name xs = do
    let srcs = Set.fromList (map (.source) xs)
    _ <- if Set.size srcs > 1
      then bad ("package " <> name <> " is provided by several sources: " <> T.intercalate ", " (Set.toList srcs))
      else Right ()
    let byVersion = Map.fromListWith (++) [(c.manifest.version, [c]) | c <- xs]
    traverse (\vs -> case vs of
      [c] -> Right c
      (c : _) -> bad ("package " <> name <> " " <> renderVersion c.manifest.version <> " is provided twice by " <> c.source)
      [] -> bad "impossible") byVersion
  bad m = Left (Err Nothing Nothing m)

data Package = Package { manifest :: Manifest, origin :: Origin }
  deriving (Eq, Show)

-- | Minimum version selection: per name the maximum of the least versions meeting
-- the reachable bounds, dependencies first.
resolve :: Manifest -> Index -> Either Err [Package]
resolve root (Index idx) = closure Map.empty root.dependencies >>= topo
 where
  closure reached [] = Right reached
  closure reached ((name, bound) : rest) = do
    c <- pick name bound
    let v = c.manifest.version
    if maybe False (Map.member v) (Map.lookup name reached)
      then closure reached rest
      else closure (Map.insertWith Map.union name (Map.singleton v c) reached) (rest ++ c.manifest.dependencies)
  pick name bound = case Map.lookup name idx of
    Nothing -> bad ("unknown package " <> name <> wanted name)
    Just versions -> case Map.lookupMin (Map.dropWhileAntitone (< bound) versions) of
      Just (_, c) -> Right c
      Nothing -> bad ("no version of " <> name <> " at or above " <> renderVersion bound
                      <> " (available: " <> T.intercalate ", " (map renderVersion (Map.keys versions)) <> ")")
  wanted name =
    let by = [m.name | m <- root : [c.manifest | vs <- Map.elems idx, c <- Map.elems vs], any ((== name) . fst) m.dependencies]
    in if null by then "" else " (required by " <> T.intercalate ", " by <> ")"
  bad m = Left (Err Nothing Nothing m)

  -- Kahn's algorithm, smallest name first
  topo reached = walk Set.empty (Map.keysSet chosen) []
   where
    chosen = Map.map (snd . Map.findMax) reached
    deps n = Set.fromList (map fst (chosen Map.! n).manifest.dependencies)
    walk done todo acc
      | Set.null todo = Right (reverse acc)
      | otherwise = case Set.lookupMin (Set.filter (\n -> deps n `Set.isSubsetOf` done) todo) of
          Just n -> walk (Set.insert n done) (Set.delete n todo) (toPackage (chosen Map.! n) : acc)
          Nothing -> bad ("dependency cycle among " <> T.intercalate ", " (Set.toList todo)
                          <> if root.name `Set.member` Set.unions (map deps (Set.toList todo)) then " (through the root package)" else "")
    toPackage c = Package c.manifest c.origin

-- * The lock file

data Locked = Locked
  { name :: Name
  , version :: Version
  , origin :: Origin
  , hash :: Text
  } deriving (Eq, Show)

renderLock :: [Locked] -> Text
renderLock ls = T.unlines $
  [ "-- project.lock: written by `caraml build`, do not edit."
  , "packages =" ]
  ++ (case ls of
        [] -> [ "  []" ]
        _ -> zipWith (\pre l -> "  " <> pre <> entry l) ("[ " : repeat ", ") ls ++ [ "  ]" ])
 where
  entry (Locked n v o h) = "(" <> T.intercalate ", " [q n, q (renderVersion v), origin o, q h] <> ")"
  origin (OriginDir p) = "Dir " <> q (T.pack p)
  origin (OriginGit u c d) = T.unwords ["Git", q u, q c, q d]
  q s = "\"" <> T.concatMap (\c -> if c == '"' || c == '\\' then T.pack ['\\', c] else T.singleton c) s <> "\""

readLock :: [(Nm, Value)] -> Either Err [Locked]
readLock fields = case fields of
  [("packages", e)] -> entries e
  _ -> bad "expected exactly one binding `packages = [...]`"
 where
  entries (VList es) = mapM entry es
  entries _ = bad "packages: expected a list"
  entry (VTuple [VStr n, VStr v, o, VStr h]) = do
    ver <- either bad Right (parseVersion v)
    org <- origin o
    pure (Locked n ver org h)
  entry _ = bad "packages: expected `(name, version, origin, hash)`"
  origin (VCon ["Dir"] [VStr p]) = Right (OriginDir (T.unpack p))
  origin (VCon ["Git"] [VStr u, VStr c, VStr d]) = Right (OriginGit u c d)
  origin _ = bad "packages: expected `Dir path` or `Git url commit subdir`"
  bad m = Left (failure ("lock: " <> m))

-- * Modules by directory and the whole program

-- | the module of @P.caraml@, @P.sig@ and @P/@
data Tree = Tree
  { decls :: Module
  , sig :: Maybe Sig
  , subs :: [(Nm, Tree)]
  } deriving (Eq, Show)

data PkgSrc = PkgSrc
  { library :: Maybe (Nm, Tree)
  , executables :: [(Text, Nm, Tree)]
  } deriving (Eq, Show)

heads :: Set Mpath -> Set Nm
heads ps = Set.fromList [h | (h : _) <- Set.toList ps]

-- | what a tree needs from the enclosing structure
treeHeads :: Tree -> Set Nm
treeHeads t = heads refs `Set.difference` Set.fromList (map fst t.subs)
 where
  refs = moduleRefs t.decls
    `Set.union` maybe Set.empty sigRefs t.sig
    `Set.union` Set.fromList [[h] | (_, sub) <- t.subs, h <- Set.toList (treeHeads sub)]

-- | siblings after those they mention, ties alphabetical
orderSiblings :: [(Nm, Tree)] -> Either Err [(Nm, Tree)]
orderSiblings subs = walk Set.empty (Map.keysSet byName) []
 where
  byName = Map.fromList subs
  needs n = treeHeads (byName Map.! n) `Set.intersection` Map.keysSet byName
  walk done todo acc
    | Set.null todo = Right (reverse acc)
    | otherwise = case Set.lookupMin (Set.filter (\n -> needs n `Set.isSubsetOf` done) todo) of
        Just n -> walk (Set.insert n done) (Set.delete n todo) ((n, byName Map.! n) : acc)
        Nothing -> Left (failure ("modules refer to each other: " <> T.intercalate ", " (Set.toList todo)))

treeSubs :: Tree -> Either Err Module
treeSubs t = mconcat <$> (orderSiblings t.subs >>= mapM (uncurry treeDecl))

-- | @module P : { sig } = { subs; decls }@
treeDecl :: Nm -> Tree -> Either Err Module
treeDecl nm t = do
  subs <- treeSubs t
  pure (submodule nm t.sig (subs <> t.decls))

-- | The whole program: the libraries in resolution order, then the executable
-- spliced at the top level.
flatten :: [(Package, PkgSrc)] -> PkgSrc -> Maybe Text -> Either Err Module
flatten deps root exe = do
  libs <- mapM lib (mapMaybe (\(_, s) -> s.library) deps ++ maybe [] pure root.library)
  main <- case exe of
    Nothing -> Right mempty
    Just b -> case [(m, t) | (b', m, t) <- root.executables, b' == b] of
      [(_, t)] -> (<> t.decls) <$> treeSubs t
      _ -> Left (failure ("no executable " <> b <> " in the manifest"))
  pure (mconcat libs <> main)
 where
  lib (nm, t) = treeDecl nm t

-- | a package uses only its own modules and its declared dependencies
dependencyCheck :: Set Nm -> Manifest -> [(Package, PkgSrc)] -> PkgSrc -> Either Err ()
dependencyCheck topLevel m deps src = mapM_ check (roots src)
 where
  declared = Set.fromList [r | (p, _) <- deps, p.manifest.name `elem` map fst m.dependencies, Just r <- [p.manifest.library]]
  own = Set.fromList (maybe [] (pure . fst) src.library ++ [n | (_, _, t) <- src.executables, (n, _) <- t.subs])
  roots s = maybe [] pure s.library ++ [(n, t) | (_, n, t) <- s.executables]
  check (nm, t) =
    let bad = Set.toList ((heads (treeRefs t) `Set.intersection` topLevel) `Set.difference` (declared `Set.union` own `Set.union` Set.singleton nm))
    in if null bad then Right ()
       else Left (failure ("package " <> m.name <> ", module " <> nm <> " uses " <> T.intercalate ", " bad
                                       <> ": not a declared dependency of " <> m.name))
  -- paths in a tree minus shadowed sub-modules
  treeRefs t = Set.filter (\p -> case p of [] -> True; (h : _) -> h `Set.notMember` Set.fromList (map fst t.subs))
    (moduleRefs t.decls `Set.union` maybe Set.empty sigRefs t.sig `Set.union` Set.unions (map (treeRefs . snd) t.subs))
