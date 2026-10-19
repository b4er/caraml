-- | @caraml build@: fetch, resolve, flatten and check a project.
module CaraML.Commands.Build
  ( Build (..)
  , build
  , Project (..)
  , resolveProject
  , programs
  ) where

import Control.Monad (forM, forM_, unless, when)
import Control.Monad.Except (liftEither, runExceptT, throwError)
import Control.Monad.Reader (ask, liftIO, runReaderT)
import Data.Set (Set)
import Data.Text (Text)
import System.Directory (doesFileExist, makeAbsolute)
import System.FilePath (joinPath, splitDirectories, takeDirectory, (</>))

import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as T

import CaraML.Cli
import CaraML.Commands.Compile (Stage (..))
import CaraML.Build.Fetch
import CaraML.Build.Project
import CaraML.Language

data Build = Build
  { emit :: Set Stage
  , lock :: Bool               -- ^ rewrite @project.lock@
  , offline :: Bool            -- ^ never clone or fetch
  , packagePath :: [FilePath]  -- ^ extra directories for packages
  , cache :: Maybe FilePath
  , exe :: Maybe Text          -- ^ executable
  } deriving (Show)

-- | A resolved project:
data Project = Project
  { manifest :: Manifest
  , dir :: FilePath
  , deps :: [(Package, PkgSrc)]
  , src :: PkgSrc
  } deriving (Show)

-- | Build the project directory
build :: Build -> FilePath -> Cli ()
build b dir = do
  manifestPath <- liftIO (findManifest dir) >>= maybe (logFatal ("no project.caraml in or above " <> T.pack dir)) pure
  cache <- liftIO (maybe defaultCache makeAbsolute b.cache)
  env <- ask
  let opts = Opts cache b.offline b.packagePath (\m -> runReaderT (logInfo m) env)
  project <- io (resolveProject opts b.lock manifestPath)
  let root = project.manifest
  forM_ project.deps $ \(p, _) ->
    logInfo ("using " <> p.manifest.name <> " " <> renderVersion p.manifest.version)
  progs <- io (pure (programs project b.exe))
  forM_ progs $ \(what, prog) -> scoped what $ do
    when (Surface `Set.member` b.emit) (io (pure (printModule prog)) >>= liftIO . T.putStr)
    io (pure (typecheck prog))
    if what == "library"
      then logInfo ("library " <> maybe "(none)" id root.library <> ": ok")
      else do
        unless (bindsValue "main" prog) (logFatal ("executable " <> what <> ": the root module does not bind main"))
        logWarn ("executable " <> what <> ": checked; code generation is not implemented")
 where
  io :: IO (Either Err a) -> Cli a
  io act = liftIO act >>= either (logFatal . renderErr) pure

-- | the programs of a project:
programs :: Project -> Maybe Text -> Either Err [(Text, Module)]
programs pr exe = case maybe (map fst pr.manifest.executables) pure exe of
  [] -> (\p -> [("library", p)]) <$> flatten pr.deps pr.src Nothing
  es -> forM es $ \e -> (,) e <$> flatten pr.deps pr.src (Just e)

-- | resolve the project: from @project.lock@ when present (check hashes), else
-- from the sources writing the lock.
resolveProject :: Opts -> Bool -> FilePath -> IO (Either Err Project)
resolveProject opts relock manifestPath = runExceptT $ do
  let rootDir = takeDirectory manifestPath
      lockPath = rootDir </> "project.lock"
  root <- readManifestFile manifestPath
  hasLock <- liftIO (doesFileExist lockPath)
  packages <- if hasLock && not relock
    then do
      src <- liftIO (T.readFile lockPath)
      locked <- liftEither (inFile lockPath (parseData src >>= readLock))
      fromLock opts rootDir locked
    else do
      index <- scanSources opts rootDir root
      resolved <- liftEither (resolve root index)
      withDirs <- forM resolved $ \p -> (,) p <$> materialise opts p
      locked <- forM withDirs $ \(p, d) -> do
        h <- liftIO (hashTree d)
        pure (Locked p.manifest.name p.manifest.version (relOrigin rootDir p.origin) h)
      liftIO (T.writeFile lockPath (renderLock locked))
      pure withDirs
  deps <- forM packages $ \(p, d) -> (,) p <$> readPkgSrc d p.manifest
  src <- readPkgSrc rootDir root
  let topLevel = Set.fromList ([r | (p, _) <- deps, Just r <- [p.manifest.library]] ++ maybe [] pure root.library)
  forM_ deps $ \(p, s) -> liftEither (dependencyCheck topLevel p.manifest deps s)
  liftEither (dependencyCheck topLevel root deps src)
  forM_ root.dependencies $ \(n, _) ->
    unless (n `elem` [p.manifest.name | (p, _) <- deps]) $
      throwError (Err (Just lockPath) Nothing ("dependency " <> n <> " is not in the lock; run with --lock"))
  pure (Project root rootDir deps src)

relOrigin :: FilePath -> Origin -> Origin
relOrigin rootDir (OriginDir d) = OriginDir (relativeTo rootDir d)
relOrigin _ o = o

relativeTo :: FilePath -> FilePath -> FilePath
relativeTo base path =
  let bs = splitDirectories base
      ps = splitDirectories path
      common = length (takeWhile id (zipWith (==) bs ps))
      parts = replicate (length bs - common) ".." ++ drop common ps
  in if null parts then "." else joinPath parts
