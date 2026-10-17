{-# LANGUAGE OverloadedStrings #-}

module CaraML.Commands.Compile where

import Data.Set (Set)

import CaraML.Cli

data Target = X64 | Wasm
  deriving (Eq, Show, Enum, Bounded)

-- intermediate languages that --emit can dump
data Stage = Surface | Core | ANF | Flat
  deriving (Eq, Ord, Show, Enum, Bounded)

data Compile = Compile { cTarget :: Target, cOut :: Maybe FilePath, cEmit :: Set Stage }

compile :: Compile -> [FilePath] -> Cli ()
compile _ _ = logFatal "compile: not implemented"
