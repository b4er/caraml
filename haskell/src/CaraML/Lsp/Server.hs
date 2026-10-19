-- | The LSP server: one reader, one writer and one dispatcher thread, plus one worker
-- per request and one diagnostics job per document.

module CaraML.Lsp.Server
  ( Server
  , Handlers (..)
  , RequestHandler
  , NotificationHandler
  , Diagnose
  , run
  , withParams
  , sendNotification
  , sendRequest
  ) where

import Control.Concurrent (ThreadId, forkIO, myThreadId, threadDelay)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Concurrent.STM
import Control.Exception
import Control.Monad (void, when)
import Control.Monad.Reader (ask, liftIO, runReaderT)
import Data.Aeson (FromJSON, Value (..), object, withObject, (.:), (.:?), (.=))
import Data.Aeson.Types (Pair, parseEither, parseJSON)
import Data.ByteString.Builder (hPutBuilder)
import Data.Foldable (for_, traverse_)
import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Version (showVersion)
import System.Exit (ExitCode (..))
import System.IO
import GHC.IO.Handle (hDuplicate, hDuplicateTo)

import qualified Data.Aeson as Json
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Utf16.Rope.Mixed as Rope

import CaraML.Cli
import CaraML.Lsp.Docs
import CaraML.Lsp.JsonRpc
import Paths_caraml_lang (version)

type RequestHandler = Server -> Docs -> Value -> Cli (Either ResponseError Value)

type NotificationHandler = Server -> Value -> Cli ()

-- | The diagnostics of one document version, as LSP @Diagnostic@ objects.
type Diagnose = Uri -> Doc -> Cli [Value]

data Handlers = Handlers
  { capabilities  :: [Pair]
  , requests      :: Map Text RequestHandler
  , notifications :: Map Text NotificationHandler
  , diagnose      :: Diagnose
  }

data Phase = Uninitialized | Running | ShuttingDown
  deriving (Eq)

data Job = Queued | Cancelled | Busy !ThreadId

data In = Msg Message | Eof

data Out = Frame BS.ByteString | Close

data Server = Server
  { input    :: TQueue In
  , output   :: TQueue Out
  , phase    :: TVar Phase
  , docs     :: TVar Docs
  , jobs     :: TVar (Map Id Job)
  , diag     :: TVar (Map Uri ThreadId)
  , pending  :: TVar (Map Id (TMVar (Either ResponseError Value)))
  , nextId   :: TVar Int
  , config   :: TVar Value
  }

-- | Thrown to a worker by @$/cancelRequest@ and to a superseded diagnostics job.
data Cancel = Cancel
  deriving (Show)

instance Exception Cancel where
  toException = asyncExceptionToException
  fromException = asyncExceptionFromException

-- | Wait between the last edit and computing diagnostics.
debounceMicros :: Int
debounceMicros = 50000

run :: Handlers -> Cli ExitCode
run hs = do
  (inp, out) <- liftIO protocolHandles
  s <- liftIO $ Server
    <$> newTQueueIO <*> newTQueueIO <*> newTVarIO Uninitialized <*> newTVarIO Map.empty
    <*> newTVarIO Map.empty <*> newTVarIO Map.empty <*> newTVarIO Map.empty <*> newTVarIO 0
    <*> newTVarIO Null
  written <- liftIO newEmptyMVar
  void $ fork (reader s inp)
  void $ fork (writer s out `finally'` liftIO (putMVar written ()))
  logInfo "started"
  code <- dispatch hs s
  liftIO $ do
    atomically (writeTQueue s.output Close)
    takeMVar written
  logInfo ("exit: " <> T.pack (show code))
  pure code

protocolHandles :: IO (Handle, Handle)
protocolHandles = do
  inp <- hDuplicate stdin
  out <- hDuplicate stdout
  hDuplicateTo stderr stdout
  withFile "/dev/null" ReadMode (`hDuplicateTo` stdin)
  for_ [inp, out] $ \h -> hSetBinaryMode h True >> hSetBuffering h (BlockBuffering Nothing)
  pure (inp, out)

reader :: Server -> Handle -> Cli ()
reader s h = loop
 where
  loop = liftIO (try (readFrame h)) >>= \case
    Left e -> logError ("read: " <> T.pack (displayException (e :: IOException))) >> eof
    Right Nothing -> eof
    Right (Just b) -> case decodeMessage b of
      Left e -> do
        logError ("malformed message: " <> T.pack e)
        logTrace ("<- " <> excerpt b)
        send s (responseFrame Nothing (Left (parseError (T.pack e))))
        loop
      Right m -> logTrace ("<- " <> excerpt b) >> route m >> loop

  route = \case
    Notification "$/cancelRequest" p ->
      either (logWarn . T.pack) (\i -> liftIO (cancel s i) >>= logCancel i)
        (parseEither (withObject "CancelParams" (.: "id")) p)
    Response i r -> do
      known <- liftIO (deliver s i r)
      if known
        then logWith Debug "response" ["id" .= i, "ok" .= either (const False) (const True) r]
        else logWith Warn "response to unknown request" ["id" .= i]
    m@(Request i _ _) -> liftIO . atomically $ do
      modifyTVar' s.jobs (Map.insert i Queued)
      writeTQueue s.input (Msg m)
    m -> liftIO (atomically (writeTQueue s.input (Msg m)))

  logCancel i c = logWith (if c == NotPending then Trace else Debug) "cancel" ["id" .= i, "was" .= show c]

  eof = logDebug "end of input" >> liftIO (atomically (writeTQueue s.input Eof))

data CancelResult = BeforeStart | Interrupted | NotPending
  deriving (Eq, Show)

cancel :: Server -> Id -> IO CancelResult
cancel s i = do
  busy <- atomically $ Map.lookup i <$> readTVar s.jobs >>= \case
    Just Queued -> Left BeforeStart <$ modifyTVar' s.jobs (Map.insert i Cancelled)
    Just (Busy t) -> pure (Right t)
    _ -> pure (Left NotPending)
  -- throwTo blocks until delivered; never stall the reader on a masked worker
  either pure (\t -> Interrupted <$ forkIO (throwTo t Cancel)) busy

deliver :: Server -> Id -> Either ResponseError Value -> IO Bool
deliver s i r = atomically $ do
  w <- Map.lookup i <$> readTVar s.pending
  for_ w $ \v -> modifyTVar' s.pending (Map.delete i) >> putTMVar v r
  pure (isJust w)

writer :: Server -> Handle -> Cli ()
writer s h = loop
 where
  loop = do
    outs <- liftIO . atomically $ (:) <$> readTQueue s.output <*> flushTQueue s.output
    let (frames, rest) = break isClose outs
    on <- enabled Trace
    when on $ for_ [b | Frame b <- frames] $ \b -> logTrace ("-> " <> excerpt b)
    r <- liftIO (try (hPutBuilder h (foldMap frame [b | Frame b <- frames]) >> hFlush h))
    case r of
      Left e -> do
        logError ("write: " <> T.pack (displayException (e :: IOException)))
        liftIO (atomically (writeTQueue s.input Eof))
      Right () -> when (null rest) loop

  isClose Close = True
  isClose _ = False

dispatch :: Handlers -> Server -> Cli ExitCode
dispatch hs s = loop
 where
  loop = liftIO (atomically (readTQueue s.input)) >>= \case
    Eof -> exitCode
    Msg (Notification "exit" _) -> do
      c <- exitCode
      when (c /= ExitSuccess) (logWarn "exit without shutdown")
      pure c
    Msg m -> step m >> loop

  exitCode = phase <&> \p -> if p == ShuttingDown then ExitSuccess else ExitFailure 1

  phase = liftIO (readTVarIO s.phase)

  step = \case
    Request i m p -> logWith Debug m ["id" .= i] >> phase >>= \case
      Uninitialized
        | m == "initialize" -> initialize i p
        | otherwise -> reject i serverNotInitialized
      ShuttingDown -> reject i (invalidRequest "server is shutting down")
      Running
        | m == "initialize" -> reject i (invalidRequest "initialize sent twice")
        | m == "shutdown" -> do
            logInfo "shutdown"
            liftIO (atomically (writeTVar s.phase ShuttingDown))
            answer i (Right Null)
        | Just h <- Map.lookup m hs.requests -> spawn s i m (h s) p
        | otherwise -> reject i (methodNotFound ("unknown method: " <> m))
    Notification m p -> phase >>= \case
      Running -> notification m p
      _ -> logDebug ("dropped " <> m <> " outside the running phase")
    Response{} -> pure ()

  reject i e = logWith Warn e.message ["id" .= i] >> answer i (Left e)

  initialize i p = do
    let client = either (const "unknown client") id . flip parseEither p . withObject "InitializeParams" $ \o ->
          o .:? "clientInfo" >>= maybe (pure "unknown client") (withObject "ClientInfo" $ \c ->
            (\n v -> n <> maybe "" (" " <>) v) <$> c .: "name" <*> c .:? "version")
    logInfo ("initialize: " <> client)
    logTrace ("initialize params: " <> excerpt (BS.toStrict (Json.encode p)))
    for_ (parseEither (withObject "InitializeParams" (.:? "initializationOptions")) p) $
      traverse_ (liftIO . atomically . writeTVar s.config)
    liftIO (atomically (writeTVar s.phase Running))
    answer i . Right $ object
      [ "capabilities" .= object
          ( "positionEncoding" .= ("utf-16" :: Text)
          : "textDocumentSync" .= object ["openClose" .= True, "change" .= (2 :: Int)]
          : hs.capabilities )
      , "serverInfo" .= object ["name" .= ("caraml" :: Text), "version" .= showVersion version]
      ]

  answer i r = liftIO . atomically $ do
    modifyTVar' s.jobs (Map.delete i)
    writeTQueue s.output (Frame (responseFrame (Just i) r))

  notification m p = case m of
    "initialized" -> pure ()
    "textDocument/didOpen" -> withNote p $ \(DidOpen uri d) -> do
      logWith Info "open" ["uri" .= uri, "version" .= d.version]
      liftIO (atomically (modifyTVar' s.docs (Map.insert uri d)))
      diagnose hs s uri
    "textDocument/didChange" -> withNote p $ \(DidChange uri v cs) -> do
      logWith Debug "change" ["uri" .= uri, "version" .= v, "edits" .= length cs]
      r <- liftIO . atomically $ Map.lookup uri <$> readTVar s.docs >>= \case
        Nothing -> pure (Left "change to a document that is not open")
        Just d -> case applyChanges d.text cs of
          Left e -> pure (Left e)
          Right t -> Right t <$ modifyTVar' s.docs (Map.insert uri (Doc v t))
      case r of
        Left e -> logError (uri <> ": " <> T.pack e)
        Right t -> do
          logWith Trace "text" ["uri" .= uri, "lines" .= Rope.lengthInLines t, "utf16" .= Rope.utf16Length t]
          diagnose hs s uri
    "textDocument/didClose" -> withNote p $ \(DidClose uri) -> do
      logWith Info "close" ["uri" .= uri]
      liftIO . atomically $ modifyTVar' s.docs (Map.delete uri)
      stopDiagnostics s uri
      liftIO (sendNotification s "textDocument/publishDiagnostics" (publish uri Nothing []))
    "workspace/didChangeConfiguration" -> do
      logDebug "configuration changed"
      logTrace ("settings: " <> excerpt (BS.toStrict (Json.encode p)))
      for_ (parseEither (withObject "DidChangeConfigurationParams" (.:? "settings")) p) $
        traverse_ (liftIO . atomically . writeTVar s.config)
    _ | Just h <- Map.lookup m hs.notifications -> guarded m (h s p)
      | "$/" `T.isPrefixOf` m -> pure ()
      | otherwise -> logWarn ("unknown notification " <> m)

  withNote :: FromJSON a => Value -> (a -> Cli ()) -> Cli ()
  withNote p k = either (\e -> logWarn ("bad params: " <> T.pack e)) k (parseEither parseJSON p)

-- | Run a request on its own thread; it replies exactly once.
spawn :: Server -> Id -> Text -> (Docs -> Value -> Cli (Either ResponseError Value)) -> Value -> Cli ()
spawn s i m h p = do
  docs <- liftIO (readTVarIO s.docs)
  env <- ask
  let cli x = runReaderT x env
  void . liftIO . forkIO $ mask $ \restore -> do
    t <- myThreadId
    go <- atomically $ Map.lookup i <$> readTVar s.jobs >>= \case
      Just Cancelled -> pure False
      _ -> True <$ modifyTVar' s.jobs (Map.insert i (Busy t))
    cli (scoped m (logWith Trace (if go then "start" else "skip, cancelled before start") ["id" .= i]))
    r <- if not go then pure (Left (toException Cancel)) else
      try . restore . cli . scoped m . timed Debug "done" $
        h docs p >>= liftIO . evaluate . responseFrame (Just i)
    uninterruptibleMask_ $ do
      b <- case r of
        Right b -> pure b
        Left e
          | Just Cancel <- fromException e -> responseFrame (Just i) (Left requestCancelled) <$
              cli (scoped m (logWith Debug "cancelled" ["id" .= i]))
          | otherwise -> responseFrame (Just i) (Left (internalError (T.pack (displayException e)))) <$
              cli (scoped m (logError (T.pack (displayException e))))
      atomically $ do
        modifyTVar' s.jobs (Map.delete i)
        writeTQueue s.output (Frame b)

-- | (Re)start the diagnostics job of a document, cancelling a running one; a job
-- publishes only if its version is still the current one.
diagnose :: Handlers -> Server -> Uri -> Cli ()
diagnose hs s uri = do
  env <- ask
  gate <- liftIO newEmptyMVar
  t <- liftIO . forkIO $ do
    takeMVar gate
    me <- myThreadId
    r <- try . flip runReaderT env . scoped "diagnostics" $ do
      liftIO (threadDelay debounceMicros)
      docs <- liftIO (readTVarIO s.docs)
      for_ (Map.lookup uri docs) $ \d -> do
        ds <- timed Trace "computed" (hs.diagnose uri d)
        b <- liftIO (evaluate (notificationFrame "textDocument/publishDiagnostics"
                                 (publish uri (Just d.version) ds)))
        current <- liftIO . atomically $ do
          cur <- Map.lookup uri <$> readTVar s.docs
          let current = fmap (.version) cur == Just d.version
          current <$ when current (writeTQueue s.output (Frame b))
        logWith (if current then Debug else Trace) (if current then "published" else "dropped, stale")
          ["uri" .= uri, "version" .= d.version, "count" .= length ds]
    case r of
      Left e | Nothing <- (fromException e :: Maybe Cancel) ->
        runReaderT (logError ("diagnostics: " <> T.pack (displayException e))) env
      _ -> pure ()
    atomically $ modifyTVar' s.diag (Map.update (\t' -> if t' == me then Nothing else Just t') uri)
  old <- liftIO . atomically $ stateTVar s.diag (\m -> (Map.lookup uri m, Map.insert uri t m))
  for_ old $ \_ -> logWith Trace "diagnostics superseded" ["uri" .= uri]
  liftIO $ do
    for_ old $ \o -> forkIO (throwTo o Cancel)
    putMVar gate ()

stopDiagnostics :: Server -> Uri -> Cli ()
stopDiagnostics s uri = liftIO $ do
  old <- atomically $ stateTVar s.diag (\m -> (Map.lookup uri m, Map.delete uri m))
  for_ old $ \o -> forkIO (throwTo o Cancel)

-- | The start of a message, for trace logs.
excerpt :: BS.ByteString -> Text
excerpt b
  | BS.length b <= 1000 = T.decodeUtf8Lenient b
  | otherwise = T.decodeUtf8Lenient (BS.take 1000 b) <> "... (" <> T.pack (show (BS.length b)) <> " bytes)"

publish :: Uri -> Maybe Int -> [Value] -> Value
publish uri v ds = object (["uri" .= uri, "diagnostics" .= ds] ++ ["version" .= x | Just x <- [v]])

-- | Decode a request's params, answering InvalidParams when they do not fit.
withParams :: FromJSON a => Value -> (a -> Cli (Either ResponseError Value)) -> Cli (Either ResponseError Value)
withParams p k = either (pure . Left . invalidParams . T.pack) k (parseEither parseJSON p)

sendNotification :: Server -> Text -> Value -> IO ()
sendNotification s m p = send' s (notificationFrame m p)

-- | A request to the client; blocks until it answers.
sendRequest :: Server -> Text -> Value -> IO (Either ResponseError Value)
sendRequest s m p = do
  (i, v) <- atomically $ do
    n <- stateTVar s.nextId (\n -> (n, n + 1))
    let i = IdText ("caraml-" <> T.pack (show n))
    v <- newEmptyTMVar
    modifyTVar' s.pending (Map.insert i v)
    writeTQueue s.output (Frame (requestFrame i m p))
    pure (i, v)
  atomically (takeTMVar v) `onException` atomically (modifyTVar' s.pending (Map.delete i))

send :: Server -> BS.ByteString -> Cli ()
send s = liftIO . send' s

send' :: Server -> BS.ByteString -> IO ()
send' s = atomically . writeTQueue s.output . Frame

-- | A notification handler failing must not take down the dispatcher.
guarded :: Text -> Cli () -> Cli ()
guarded m act = do
  env <- ask
  r <- liftIO (try (runReaderT act env))
  for_ (either Just (const Nothing) r) $ \e -> case fromException e of
    Just (ec :: ExitCode) -> liftIO (throwIO ec)
    Nothing -> logError (m <> ": " <> T.pack (displayException (e :: SomeException)))

fork :: Cli () -> Cli ThreadId
fork act = ask >>= \env -> liftIO (forkIO (runReaderT act env))

finally' :: Cli a -> Cli () -> Cli a
finally' act after = ask >>= \env -> liftIO (runReaderT act env `finally` runReaderT after env)
