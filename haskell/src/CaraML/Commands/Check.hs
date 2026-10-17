{-# LANGUAGE OverloadedStrings #-}

module CaraML.Commands.Check where

import CaraML.Cli

data Check = Check

check :: Check -> [FilePath] -> Cli ()
check _ _ = logFatal "check: not implemented"
