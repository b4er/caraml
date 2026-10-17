{-# LANGUAGE OverloadedStrings #-}

module CaraML.Cli
  ( Cli
  , Global (..)
  , Env (..)
  , runCli
  , LogLevel (..)
  , Logger
  , scoped
  , enabled
  , logAt
  , logWith
  , logFatal
  , logError
  , logWarn
  , logInfo
  , logDebug
  , logTrace
  , timed
  ) where

import Control.Monad (when)
import Control.Monad.Reader (ReaderT, asks, liftIO, local, runReaderT)
import Data.Aeson (Value, object, (.=))
import Data.Aeson.Key (Key)
import Data.Char (toLower)
import Data.Text (Text)
import GHC.Clock (getMonotonicTime)
import System.Exit (ExitCode (..), exitWith)
import System.IO (stderr)

import qualified Data.Aeson as Json
import qualified Data.Aeson.Key as Key
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text as T
import qualified Data.Text.Encoding as T

data LogLevel = Error | Warn | Info | Debug | Trace
  deriving (Eq, Ord, Show, Enum, Bounded)

data Global = Global { gLogLevel :: LogLevel, gJson :: Bool }

data Logger = Logger { lLevel :: LogLevel, lJson :: Bool, lScope :: [Text] }

data Env = Env { envGlobal :: Global, envLogger :: Logger }

type Cli = ReaderT Env IO

runCli :: Global -> Cli a -> IO a
runCli g m = runReaderT m (Env g (Logger (gLogLevel g) (gJson g) []))

scoped :: Text -> Cli a -> Cli a
scoped s = local (\e -> e { envLogger = (envLogger e) { lScope = lScope (envLogger e) ++ [s] } })

enabled :: LogLevel -> Cli Bool
enabled lvl = asks ((lvl <=) . lLevel . envLogger)

logAt :: LogLevel -> Text -> Cli ()
logAt lvl msg = emit lvl msg []

-- | A message with structured fields (@k=v@ in text, keys in JSON).
logWith :: LogLevel -> Text -> [(Key, Value)] -> Cli ()
logWith = emit

logError, logWarn, logInfo, logDebug, logTrace :: Text -> Cli ()
logError = logAt Error
logWarn  = logAt Warn
logInfo  = logAt Info
logDebug = logAt Debug
logTrace = logAt Trace

logFatal :: Text -> Cli a
logFatal msg = logError msg >> liftIO (exitWith (ExitFailure 1))

timed :: LogLevel -> Text -> Cli a -> Cli a
timed lvl msg act = do
  on <- enabled lvl
  if not on then act else do
    t0 <- liftIO getMonotonicTime
    x <- act
    t1 <- liftIO getMonotonicTime
    let ms = fromIntegral (round ((t1 - t0) * 1e5) :: Integer) / 100 :: Double
    emit lvl msg ["ms" .= ms]
    pure x

emit :: LogLevel -> Text -> [(Key, Value)] -> Cli ()
emit lvl msg extra = do
  lg <- asks envLogger
  when (lvl <= lLevel lg) $ liftIO $ BS.hPut stderr (line lg <> "\n")
 where
  name = T.pack (map toLower (show lvl))
  line lg
    | lJson lg = LBS.toStrict . Json.encode . object $
        ["level" .= name, "msg" .= msg]
        ++ ["scope" .= scope lg | not (null (lScope lg))]
        ++ extra
    | otherwise = T.encodeUtf8 $
        "[" <> name <> "] "
        <> (if null (lScope lg) then "" else scope lg <> ": ")
        <> msg
        <> foldMap (\(k, v) -> "  " <> Key.toText k <> "="
                                 <> T.decodeUtf8 (LBS.toStrict (Json.encode v))) extra
  scope = T.intercalate "/" . lScope
