{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module CaraML.Commands.Lsp where

import Control.Monad.Reader (liftIO)
import System.Exit (ExitCode (..), exitWith)

import CaraML.Cli
import CaraML.Lsp.Handlers (handlers)

import qualified CaraML.Lsp.Server as Server

data LSP = LSP

lsp :: LSP -> [FilePath] -> Cli ()
lsp _ (_ : _) = logFatal "lsp: takes no arguments"
lsp _ [] = scoped "lsp" (Server.run handlers) >>= \case
  ExitSuccess -> pure ()
  code -> liftIO (exitWith code)
