{-# LANGUAGE OverloadedStrings #-}

module CaraML.Commands.Fmt where

import CaraML.Cli

data Fmt = Fmt { fCheck :: Bool, fStdin :: Bool }

fmt :: Fmt -> [FilePath] -> Cli ()
fmt _ _ = logFatal "fmt: not implemented"
