{-# LANGUAGE AllowAmbiguousTypes #-}

module Main (main) where

import Data.Char (toLower)
import Data.List (intercalate)
import Data.Version (showVersion)
import Options.Applicative
import Options.Applicative.Help.Pretty (fill, indent, pretty, vsep)

import qualified Data.Set as Set

import CaraML.Cli
import CaraML.Commands
import Paths_caraml_lang (version)

main :: IO ()
main = customExecParser (prefs (showHelpOnEmpty <> helpShowGlobals)) parser'
   >>= uncurry runCli
 where
  parser' = info (parser <**> ((.) <$> helper <*> simpleVersioner (showVersion version)))
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
  [ command "build"   (tool (progDesc "Build a project" <> stages) build buildOptions dir)
  , command "compile" (tool (progDesc "Compile files" <> stages) compile compileOptions (some file))
  , command "fmt"     (tool (progDesc "Format files in place") fmt fmtOptions (many file))
  , command "lsp"     (tool (progDesc "Run the language server") lsp lspOptions (pure []))
  ]
 where
  tool m f opts files = info (f <$> opts <*> files) m
  file = strArgument (metavar "FILE..." <> action "file")
  dir = strArgument (metavar "DIR" <> value "." <> action "directory" <> help "Project directory (default: .)")

buildOptions :: Parser Build
buildOptions = Build
  <$> emit
  <*> switch (long "lock" <> help "Resolve afresh and rewrite project.lock")
  <*> switch (long "offline" <> help "Never clone or fetch; fail on what the cache lacks")
  <*> many (strOption (long "package-path" <> metavar "DIR" <> help "A directory of packages (repeatable)"))
  <*> optional (strOption (long "cache" <> metavar "DIR" <> help "The cache (default: $CARAML_CACHE or ~/.cache/caraml)"))
  <*> optional (strOption (long "exe" <> metavar "NAME" <> help "Build one executable"))

compileOptions :: Parser Compile
compileOptions = Compile
  <$> enumOption "cede generation target"
        (short 't' <> long "target" <> metavar "TARGET" <> value X64 <> showDefaultWith enumName)
  <*> optional (strOption (short 'o' <> long "output" <> metavar "PATH" <> help "Output file"))
  <*> emit

fmtOptions :: Parser Fmt
fmtOptions = Fmt
  <$> switch (long "check" <> help "Exit 1 if anything would change")
  <*> switch (long "stdin" <> help "Read stdin, write stdout")

lspOptions :: Parser LSP
lspOptions = pure LSP

emit :: Parser (Set.Set Stage)
emit = Set.fromList <$> many (option enumReader (long "emit" <> metavar "STAGE"
  <> help "Dump an intermediate language (see below)" <> completeWith (enumNames @Stage)))

stages :: InfoMod a
stages = footerDoc . Just $ vsep ("Stages:" : map entry
  [ (Surface, "The surface program")
  , (Core, "The core calculus, after elaboration")
  , (ANF, "A-normal form")
  , (Flat, "Closure-converted first-order code")
  ])
 where
  entry (s, brief) = indent 2 (fill 25 (pretty (enumName s)) <> pretty (brief :: String))

-- utils:

enumOption :: forall a. (Show a, Enum a, Bounded a) => String -> Mod OptionFields a -> Parser a
enumOption h m = option enumReader
  (m <> help (h ++ ": " ++ intercalate " | " (enumNames @a)) <> completeWith (enumNames @a))

enumReader :: forall a. (Show a, Enum a, Bounded a) => ReadM a
enumReader = eitherReader parse
 where
  parse s = maybe (Left ("expected one of " ++ intercalate " | " (enumNames @a))) Right
    (lookup s (zip (enumNames @a) [minBound .. maxBound]))

enumNames :: forall a. (Show a, Enum a, Bounded a) => [String]
enumNames = map enumName [minBound .. maxBound :: a]

enumName :: Show a => a -> String
enumName = map toLower . show
