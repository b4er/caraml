{-# LANGUAGE AllowAmbiguousTypes #-}

module Main (main) where

import Data.Char (toLower)
import Data.List (intercalate)
import Data.Version (showVersion)
import Options.Applicative

import qualified Data.Set as Set

import CaraML.Cli
import CaraML.Commands
import Paths_caraml (version)

main :: IO ()
main = customExecParser (prefs (showHelpOnEmpty <> helpShowGlobals)) parser'
   >>= uncurry runCli
 where
  parser' = info (helper <*> simpleVersioner (showVersion version) <*> parser)
    (fullDesc <> progDesc "CaraML compiler and tools.")

parser :: Parser (Global, Cli ())
parser = (,) <$> global <*> commands

global :: Parser Global
global = Global <$> logLevel <*> switch (long "json" <> help "Machine-readable diagnostics")
 where
  logLevel = adjust
    <$> count (short 'v' <> long "verbose" <> help "More log output (repeatable)")
    <*> count (short 'q' <> long "quiet" <> help "Less log output (repeatable)")
  count = fmap length . many . flag' ()

  adjust v q = max minBound (min maxBound (toEnum (fromEnum Warn + v - q)))

commands :: Parser (Cli ())
commands = hsubparser $ mconcat
  [ command "check"   (tool "Typecheck files" check (pure Check) (some file))
  , command "compile" (tool "Compile files" compile compileOptions (some file))
  , command "fmt"     (tool "Format files in place" fmt fmtOptions (many file))
  , command "lsp"     (tool "Run the language server" lsp lspOptions (pure []))
  ]
 where
  tool d f opts files = info (f <$> opts <*> files) (progDesc d)
  file = strArgument (metavar "FILE..." <> action "file")

compileOptions :: Parser Compile
compileOptions = Compile
  <$> enumOption "code generation target"
        (short 't' <> long "target" <> metavar "TARGET" <> value X64 <> showDefaultWith enumName)
  <*> optional (strOption (short 'o' <> long "output" <> metavar "PATH" <> help "output file"))
  <*> (Set.fromList <$> many (enumOption "dump an intermediate language (repeatable)"
        (long "emit" <> metavar "STAGE")))

fmtOptions :: Parser Fmt
fmtOptions = Fmt
  <$> switch (long "check" <> help "exit 1 if anything would change")
  <*> switch (long "stdin" <> help "read stdin, write stdout")

lspOptions :: Parser LSP
lspOptions = pure LSP

-- utils:

enumOption :: forall a. (Show a, Enum a, Bounded a) => String -> Mod OptionFields a -> Parser a
enumOption h m = option (eitherReader parse) (m <> help (h ++ ": " ++ choices) <> completeWith names)
 where
  names = map enumName [minBound .. maxBound :: a]
  choices = intercalate " | " names
  parse s = maybe (Left ("expected one of " ++ choices)) Right (lookup s (zip names [minBound .. maxBound]))

enumName :: Show a => a -> String
enumName = map toLower . show
