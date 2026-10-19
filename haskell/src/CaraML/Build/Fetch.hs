module CaraML.Build.Fetch
  ( Fetch
  , Opts (..)
  , defaultCache
  , scanSources
  , materialise
  , fromLock
  , hashTree
  , readPkgSrc
  , readManifestFile
  , findManifest
  ) where

import Control.Monad (filterM, forM, unless, when)
import Control.Monad.Except (ExceptT, catchError, liftEither, throwError)
import Control.Monad.Reader (liftIO)
import Data.Char (isAlphaNum)
import Data.List (isSuffixOf, sort)
import Data.Maybe (catMaybes, listToMaybe)
import Data.Text (Text)
import System.Directory
import System.Environment (getEnvironment, lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode)
import Text.Printf (printf)

import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.IO as T

import CaraML.Build.Project
import CaraML.Language

type Fetch = ExceptT Err IO

data Opts = Opts
  { cache :: FilePath
  , offline :: Bool               -- ^ never clone or fetch
  , packagePath :: [FilePath]     -- ^ extra @Dir@ sources
  , log :: Text -> IO ()
  }

-- | @$CARAML_CACHE@, else @$XDG_CACHE_HOME/caraml@
defaultCache :: IO FilePath
defaultCache = lookupEnv "CARAML_CACHE" >>= maybe (getXdgDirectory XdgCache "caraml") pure

failWith :: Text -> Fetch a
failWith m = throwError (failure m)

fromFile :: FilePath -> Either Err a -> Fetch a
fromFile path = liftEither . inFile path

-- * Manifests

readManifestFile :: FilePath -> Fetch Manifest
readManifestFile path = do
  src <- liftIO (T.readFile path)
  fromFile path (parseData src >>= readManifest)

-- | The manifest in a directory or one of its parents.
findManifest :: FilePath -> IO (Maybe FilePath)
findManifest dir = do
  abs' <- makeAbsolute dir
  let parents = takeWhile (\d -> d /= takeDirectory d) (iterate takeDirectory abs') ++ [takeDrive abs']
  listToMaybe <$> filterM doesFileExist (map (</> "project.caraml") parents)

-- * The index

-- | The index from the root's sources, the package path, and the @Git@ sources of
-- every manifest reached; @Dir@ paths are relative to the root.
scanSources :: Opts -> FilePath -> Manifest -> Fetch Index
scanSources opts rootDir root =
  walk Set.empty (map (Dir . (rootDir </>)) opts.packagePath ++ map relative root.sources) []
    >>= liftEither . buildIndex
 where
  relative (Dir p) = Dir (rootDir </> p)
  relative s = s
  walk _ [] acc = pure acc
  walk seen (s : rest) acc
    | s `Set.member` seen = walk seen rest acc
    | otherwise = do
        cs <- scan opts s
        let gits = [g | c <- cs, g@(Git _) <- c.manifest.sources]
        walk (Set.insert s seen) (rest ++ gits) (acc ++ cs)

scan :: Opts -> Source -> Fetch [Candidate]
scan _ (Dir dir) = do
  ok <- liftIO (doesDirectoryExist dir)
  unless ok (failWith ("source directory does not exist: " <> T.pack dir))
  entries <- liftIO (sort <$> listDirectory dir)
  pkgs <- liftIO (filterM (\e -> doesFileExist (dir </> e </> "project.caraml")) entries)
  forM pkgs $ \e -> do
    m <- readManifestFile (dir </> e </> "project.caraml")
    pure (Candidate (T.pack ("Dir " <> dir)) m (OriginDir (dir </> e)))
scan opts (Git url) = do
  bare <- ensureClone opts url
  tags <- T.lines <$> git bare ["tag", "--list", "v*"]
  fmap concat . forM [(t, v) | t <- tags, Right v <- [parseVersion (T.drop 1 t)]] $ \(tag, v) -> do
    commit <- T.strip <$> git bare ["rev-parse", tag <> "^{commit}"]
    pkgs <- gitPackages bare commit
    forM pkgs $ \(sub, m) -> do
      when (m.version /= v) $
        failWith ("tag " <> tag <> " of " <> url <> (if T.null sub then "" else " (" <> sub <> ")")
                  <> " states version " <> renderVersion m.version)
      pure (Candidate ("Git " <> url) m (OriginGit url commit sub))

-- | The manifests at the root and one level deep of a commit.
gitPackages :: FilePath -> Text -> Fetch [(Text, Manifest)]
gitPackages bare commit = do
  dirs <- filter (not . T.null) . T.lines <$> git bare ["ls-tree", "--name-only", commit]
  fmap catMaybes . forM ("" : dirs) $ \d -> do
    let obj = commit <> ":" <> (if T.null d then "" else d <> "/") <> "project.caraml"
    exists <- gitOk bare ["cat-file", "-e", obj]
    if not exists then pure Nothing else do
      src <- git bare ["cat-file", "-p", obj]
      Just . (,) d <$> fromFile (bare <> ":" <> T.unpack obj) (parseData src >>= readManifest)

-- | The bare clone of a repository, fetched unless offline.
ensureClone :: Opts -> Text -> Fetch FilePath
ensureClone opts url = do
  let bare = opts.cache </> "git" </> urlKey url
  exists <- liftIO (doesDirectoryExist bare)
  case (exists, opts.offline) of
    (True, True) -> pure ()
    (True, False) -> do
      liftIO (opts.log ("fetching " <> url))
      () <$ git bare ["fetch", "--quiet", "--tags", "--prune", "origin"]
    (False, True) -> failWith ("offline and not in the cache: " <> url)
    (False, False) -> do
      liftIO (opts.log ("cloning " <> url))
      liftIO (createDirectoryIfMissing True (takeDirectory bare))
      () <$ runGit [] ["clone", "--quiet", "--bare", T.unpack url, bare]
  pure bare

sha256Hex :: B.ByteString -> String
sha256Hex = concatMap (printf "%02x") . B.unpack . SHA256.hash

urlKey :: Text -> FilePath
urlKey url = take 16 (sha256Hex (T.encodeUtf8 url)) ++ "-" ++ map safe (T.unpack (T.takeEnd 24 url))
 where
  safe c = if isAlphaNum c then c else '_'

-- | The directory of a package's tree; @Git@ packages are checked out into the cache.
materialise :: Opts -> Package -> Fetch FilePath
materialise _ (Package _ (OriginDir d)) = pure d
materialise opts (Package m (OriginGit url commit sub)) = do
  let dir = opts.cache </> "pkg" </> T.unpack (m.name <> "-" <> renderVersion m.version <> "-" <> T.take 12 commit)
  exists <- liftIO (doesDirectoryExist dir)
  unless exists $ do
    bare <- ensureClone opts url
    have <- gitOk bare ["cat-file", "-e", commit <> "^{commit}"]
    unless have (failWith ("commit " <> commit <> " is not in " <> url))
    let tmp = dir ++ ".tmp"
        index = tmp ++ ".index"
        tree = commit <> (if T.null sub then "" else ":" <> sub)
        gitTmp args = runGit [("GIT_INDEX_FILE", index)] (["--git-dir=" ++ bare, "--work-tree=" ++ tmp] ++ args)
        cleanup = liftIO (removePathForcibly index)
    liftIO (removePathForcibly tmp >> createDirectoryIfMissing True tmp)
    (gitTmp ["read-tree", T.unpack tree] >> gitTmp ["checkout-index", "-a", "-f"] >> cleanup)
      `catchError` \e -> cleanup >> liftIO (removePathForcibly tmp) >> throwError e
    liftIO (renameDirectory tmp dir)
  pure dir

-- | The packages of a lock, with their hashes checked.
fromLock :: Opts -> FilePath -> [Locked] -> Fetch [(Package, FilePath)]
fromLock opts rootDir ls = forM ls $ \l -> do
  let origin = case l.origin of
        OriginDir p -> OriginDir (rootDir </> p)
        o -> o
  m0 <- case origin of
    OriginDir d -> readManifestFile (d </> "project.caraml")
    OriginGit {} -> pure (Manifest l.name l.version [] [] Nothing [])
  dir <- materialise opts (Package m0 origin)
  m <- readManifestFile (dir </> "project.caraml")
  h <- liftIO (hashTree dir)
  when (m.name /= l.name || m.version /= l.version) $
    failWith ("lock: " <> l.name <> " " <> renderVersion l.version <> " is "
              <> m.name <> " " <> renderVersion m.version <> " on disk")
  unless (h == l.hash) $
    failWith ("lock: hash of " <> l.name <> " changed: expected " <> l.hash <> ", found " <> h)
  pure (Package m origin, dir)

-- | @sha256:@ over (path, size, content) of the files in path order, without the
-- lock file and @.git@.
hashTree :: FilePath -> IO Text
hashTree root = do
  files <- walk ""
  parts <- forM files $ \f -> do
    content <- B.readFile (root </> f)
    pure (B.concat [BC.pack f, B.singleton 0, BC.pack (show (B.length content)), B.singleton 0, content])
  pure ("sha256:" <> T.pack (sha256Hex (B.concat parts)))
 where
  walk rel = do
    entries <- sort <$> listDirectory (root </> rel)
    fmap concat . forM entries $ \e -> do
      let p = if null rel then e else rel </> e
      isDir <- doesDirectoryExist (root </> p)
      if e == ".git" || (null rel && e == "project.lock") then pure []
        else if isDir then walk p else pure [p]

-- * Modules

-- | @src/@ of a package as module trees, every entry under a root of the manifest.
readPkgSrc :: FilePath -> Manifest -> Fetch PkgSrc
readPkgSrc dir m = do
  let src = dir </> "src"
      roots = maybe [] pure m.library ++ map snd m.executables
  exists <- liftIO (doesDirectoryExist src)
  unless exists (throwError (Err (Just src) Nothing "no src/ directory"))
  entries <- liftIO (sort <$> listDirectory src)
  let stray = [e | e <- entries, T.pack (takeBaseName e) `notElem` roots, e /= "project.caraml"]
  unless (null stray) $
    throwError (Err (Just src) Nothing ("not under a root module of the manifest: " <> T.pack (unwords stray)))
  PkgSrc
    <$> traverse (\n -> (,) n <$> readTree src n) m.library
    <*> forM m.executables (\(b, n) -> (,,) b n <$> readTree src n)

-- | The module @nm@ from @dir/nm.caraml@, @dir/nm.sig@ and @dir/nm/@.
readTree :: FilePath -> Nm -> Fetch Tree
readTree dir nm = do
  let base = dir </> T.unpack nm
  hasFile <- liftIO (doesFileExist (base <.> "caraml"))
  hasSig <- liftIO (doesFileExist (base <.> "sig"))
  hasDir <- liftIO (doesDirectoryExist base)
  decls <- if hasFile then parseWith parseModule (base <.> "caraml") else pure mempty
  sig <- if hasSig then Just <$> parseWith parseSig (base <.> "sig") else pure Nothing
  subs <- if not hasDir then pure [] else do
    entries <- liftIO (sort <$> listDirectory base)
    let names = Set.toList (Set.fromList [takeBaseName e | e <- entries, isModule e])
        badNames = filter (not . isModuleName . T.pack) names
    unless (null badNames) $
      throwError (Err (Just base) Nothing ("not a module name: " <> T.pack (unwords badNames)))
    forM names $ \n -> (,) (T.pack n) <$> readTree base (T.pack n)
  pure (Tree decls sig subs)
 where
  isModule e = ".caraml" `isSuffixOf` e || ".sig" `isSuffixOf` e || '.' `notElem` e
  parseWith p path = liftIO (T.readFile path) >>= fromFile path . p

-- * git

git :: FilePath -> [Text] -> Fetch Text
git bare args = runGit [] (("--git-dir=" ++ bare) : map T.unpack args)

gitOk :: FilePath -> [Text] -> Fetch Bool
gitOk bare args = (True <$ git bare args) `catchError` const (pure False)

runGit :: [(String, String)] -> [String] -> Fetch Text
runGit extra args = do
  parent <- liftIO getEnvironment
  (code, out, err) <- liftIO (readCreateProcessWithExitCode (proc "git" args) { env = Just (extra ++ parent) } "")
  case code of
    ExitSuccess -> pure (T.pack out)
    ExitFailure n -> failWith ("git " <> T.unwords (map T.pack args) <> " failed (" <> T.pack (show n) <> "): "
                               <> T.strip (T.pack err))
