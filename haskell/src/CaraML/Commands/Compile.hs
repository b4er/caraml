module CaraML.Commands.Compile where

import Control.Monad (forM_, when)
import Control.Monad.Reader (liftIO)
import Data.Set (Set)
import System.Directory (doesDirectoryExist)

import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as T

import CaraML.Cli
import CaraML.Language

data Target = X64 | Wasm
  deriving (Eq, Show, Enum, Bounded)

-- intermediate languages that --emit can dump
data Stage = Surface | Core | ANF | Flat
  deriving (Eq, Ord, Show, Enum, Bounded)

data Compile = Compile
  { target :: Target
  , out :: Maybe FilePath
  , emit :: Set Stage
  }

compile :: Compile -> [FilePath] -> Cli ()
compile c paths = forM_ paths $ \p -> do
  isDir <- liftIO (doesDirectoryExist p)
  when isDir (logFatal (T.pack p <> " is a directory: use `caraml build`"))
  prog <- liftIO (parseModule <$> T.readFile p) >>= fatal p
  when (Surface `Set.member` c.emit) (fatal p (printModule prog) >>= liftIO . T.putStr)
  fatal p (typecheck prog)
  when (Set.null c.emit) (logFatal "compile: code generation is not implemented")
 where
  fatal q = either (logFatal . renderErr) pure . inFile q
