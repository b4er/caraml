{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import Control.Monad (foldM)
import Control.Monad.IO.Class (liftIO)
import Data.Char (toLower)
import Data.List (intercalate)
import qualified Data.Set as Set
import System.Console.GetOpt
import System.Environment (getArgs)
import System.Exit
import System.IO

import CaraML.Commands
import CaraML.Cli

class Tool a where
  def     :: a
  options :: [Opt a]
  usage   :: String

instance Tool LSP where
  def = LSP
  options = [Option "" ["stdio"] (NoArg Right) "talk over stdin/stdout (the default)"]
  usage = "lsp [--stdio]"

instance Tool Check where
  def = Check
  options = []
  usage = "check FILES..."

instance Tool Compile where
  def = Compile X64 Nothing Set.empty
  options =
    [ Option "t" ["target"]
        (ReqArg (\s c -> (\t -> c { cTarget = t }) <$> enumArg s) "TARGET")
        (choicesOf @Target)
    , Option "o" ["output"] (ReqArg (\s c -> Right c { cOut = Just s }) "PATH") "output file"
    , Option "" ["emit"]
        (ReqArg (\s c -> (\st -> c { cEmit = Set.insert st (cEmit c) }) <$> enumArg s) "STAGE")
        ("dump IL (repeatable): " ++ choicesOf @Stage)
    ]
  usage = "compile [OPTIONS] FILES...\n" 

instance Tool Fmt where
  def = Fmt False False
  options = 
    [ Option "" ["check"] (NoArg $ \f -> Right f { fCheck = True }) "exit 1 if anything would change"
    , Option "" ["stdin"] (NoArg $ \f -> Right f { fStdin = True }) "read stdin, write stdout"
    ]
  usage = "fmt [OPTIONS] [FILES...]\n"


globalOptions :: [Opt Global]
globalOptions =
  [ Option "v" ["verbose"] (NoArg $ \g -> Right g { gLogLevel = up (gLogLevel g) })
      "more log output (repeatable)"
  , Option "q" ["quiet"] (NoArg $ \g -> Right g { gLogLevel = down (gLogLevel g) })
      "less log output (repeatable)"
  , Option "" ["log-level"]
      (ReqArg (\s g -> (\l -> g { gLogLevel = l }) <$> enumArg s) "LEVEL")
      (choicesOf @LogLevel)
  , Option ""  ["json"]    (NoArg $ \g -> Right g { gJson = True })        "machine-readable diagnostics"
  ]

-- one step along a bounded enumeration, stopping at its ends
up, down :: (Eq a, Enum a, Bounded a) => a -> a
up x   = if x == maxBound then x else succ x
down x = if x == minBound then x else pred x

-- an option updates the settings or rejects its argument
type Opt a = OptDescr (a -> Either String a)

data Flag a = Help | Set (a -> Either String a)

parseWith :: ArgOrder (Flag a) -> String -> [Opt a] -> a
          -> [String] -> IO (a, [String])
parseWith order u opts x as = case getOpt order ds as of
  (fs, rest, []) | any isHelp fs -> putStr (usageInfo' u ds) >> exitSuccess
                 | otherwise     -> either (\e -> failWith [e ++ "\n"]) (pure . (, rest))
                                      (foldM (flip app) x fs)
  (_, _, es)     -> failWith es
 where
  ds = withHelp opts

  failWith es = hPutStr stderr (concat es ++ usageInfo' u ds) >> exitWith (ExitFailure 2)

  isHelp Help = True
  isHelp _ = False

  app Help = Right
  app (Set f) = f

enumName :: Show a => a -> String
enumName = map toLower . show

choicesOf :: forall a. (Show a, Enum a, Bounded a) => String
choicesOf = intercalate " | " (map enumName [minBound .. maxBound :: a])

enumArg :: forall a. (Show a, Enum a, Bounded a) => String -> Either String a
enumArg s = case [x | x <- [minBound .. maxBound], enumName x == s] of
  [x] -> Right x
  _   -> Left ("unknown value " ++ show s ++ ", expected " ++ choicesOf @a)

usageInfo' :: String -> [OptDescr a] -> String
usageInfo' = usageInfo . ("Usage: caraml " ++)

withHelp :: [Opt a] -> [OptDescr (Flag a)]
withHelp opts = Option "h" ["help"] (NoArg Help) "show this help" : map (fmap Set) opts

runTool :: forall a. Tool a => (a -> [FilePath] -> Cli ()) -> [String] -> Cli ()
runTool f as = liftIO (parseWith Permute (usage @a ++ "\n") options def as) >>= uncurry f

main :: IO ()
main = do
  (g, cmd) <- parseWith RequireOrder usage' globalOptions (Global Warn False) =<< getArgs
  app <- case cmd of
    "check" : as -> pure (runTool check as)
    "compile" : as -> pure (runTool compile as)
    "fmt" : as -> pure (runTool fmt as)
    "lsp" : as -> pure (runTool lsp as)
    c : _ -> usageErr ("unknown command: " ++ c)
    [] -> usageErr "missing COMMAND"
  runCli g app
 where
   usageErr s = hPutStr stderr (s ++ "\n\n" ++ usageInfo' usage' (withHelp globalOptions)) >> exitWith (ExitFailure 2)

   usage' = unlines
     [ "[OPTIONS] COMMAND [ARGS]\n"
     , "Commands: check  compile  run  fmt  lsp\n"
     , "Options:"
     ]