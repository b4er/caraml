module CaraML.Commands.Fmt where

import Control.Monad (forM_, when)
import Control.Monad.Reader (liftIO)

import qualified Data.Text as T
import qualified Data.Text.IO as T

import CaraML.Cli
import CaraML.Language

data Fmt = Fmt { check :: Bool, stdin :: Bool }

-- | Parse and print each file, rewriting it in place; with @--check@ only report
-- the files that would change.
fmt :: Fmt -> [FilePath] -> Cli ()
fmt f paths
  | f.stdin = liftIO T.getContents >>= fatal . format >>= liftIO . T.putStr
  | otherwise = forM_ paths $ \p -> do
      src <- liftIO (T.readFile p)
      out <- fatal (inFile p (format src))
      when (out /= src) $
        if f.check
          then logFatal (T.pack p <> ": not formatted")
          else liftIO (T.writeFile p out)
 where
  format src = parseModule src >>= printModule
  fatal = either (logFatal . renderErr) pure
