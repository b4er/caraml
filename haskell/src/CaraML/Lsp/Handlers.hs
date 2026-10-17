{-# LANGUAGE OverloadedStrings #-}

-- | The language features. All mocked: they exercise the server, not the checker.
module CaraML.Lsp.Handlers (handlers) where

import Control.Concurrent (threadDelay)
import Control.Monad.Reader (liftIO)
import Data.Aeson (Value (..), object, withObject, (.:), (.=))
import Data.Aeson.Types (parseEither)
import Data.Char (isAlphaNum, isAsciiLower, isAsciiUpper, isLetter, isUpper)
import Data.Maybe (listToMaybe)
import Data.Text (Text)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Utf16.Rope.Mixed as Rope

import CaraML.Cli
import CaraML.Lsp.Abbreviations
import CaraML.Lsp.Docs
import CaraML.Lsp.JsonRpc
import CaraML.Lsp.Server

handlers :: Handlers
handlers = Handlers
  { hCapabilities =
      [ "hoverProvider" .= True
      , "completionProvider" .= object ["triggerCharacters" .= ["\\" :: Text]]
      ]
  , hRequests = Map.fromList
      [ ("textDocument/hover", hover)
      , ("textDocument/completion", completion)
      , ("caraml/sleep", sleep)
      ]
  , hNotifications = Map.empty
  , hDiagnose = \_ _ -> pure []
  }

-- | The identifier under the cursor and the document version.
hover :: RequestHandler
hover _ docs p = withParams p $ \(At uri (Position l c)) ->
  pure . Right $ case Map.lookup uri docs of
    Nothing -> Null
    Just d -> object
      [ "contents" .= object
          [ "kind" .= ("markdown" :: Text)
          , "value" .= ("`" <> word (lineAt l (docText d)) c <> "` at " <> T.pack (show l) <> ":"
                         <> T.pack (show c) <> ", version " <> T.pack (show (docVersion d)))
          ]
      ]
 where
  word line c = case splitAtPosition (Position 0 c) line of
    Nothing -> ""
    Just (a, b) -> T.takeWhileEnd ident (Rope.toText a) <> T.takeWhile ident (Rope.toText b)
  ident = identChar

-- | After @\\name@ the abbreviations, replacing it; otherwise the keywords and the
-- identifiers of the document. No scopes and no types yet.
completion :: RequestHandler
completion _ docs p = withParams p $ \(At uri (Position l c)) ->
  pure . Right $ case Map.lookup uri docs of
    Nothing -> Null
    Just d ->
      let before = maybe mempty fst (splitAtPosition (Position 0 c) (lineAt l (docText d)))
          end = Rope.utf16Length before
          typed = Rope.toText before
          items = case pendingAbbreviation typed of
            Just n ->
              let start = Position l (end - fromIntegral (T.length n) - 1)
              in map (abbreviation start (Position l end)) abbreviations
            Nothing -> map (item 14 "keyword") keywords
              ++ [ item (if isUpper (T.head w) then 9 else 6) "in this document" w
                 | w <- Set.toList (identifiers (Rope.toText (docText d)))
                 , w /= T.takeWhileEnd identChar typed
                 ]
      in object ["isIncomplete" .= False, "items" .= items]
 where
  item :: Int -> Text -> Text -> Value
  item k detail w = object ["label" .= w, "kind" .= k, "detail" .= detail]
  abbreviation s e (k, v) = object
    [ "label" .= ("\\" <> k)
    , "labelDetails" .= object ["description" .= v]
    , "kind" .= (1 :: Int)
    , "filterText" .= ("\\" <> k)
    , "textEdit" .= object
        ["range" .= object ["start" .= position s, "end" .= position e], "newText" .= v]
    ]

-- | The @name@ of a @\\name@ that ends the text, as the editors' rewriters see it.
pendingAbbreviation :: Text -> Maybe Text
pendingAbbreviation t = listToMaybe
  [ n
  | n <- [T.takeWhileEnd (\x -> isAsciiLower x || isAsciiUpper x) t, T.takeWhileEnd symbol t]
  , "\\" `T.isSuffixOf` T.dropEnd (T.length n) t
  ]
 where
  symbol = (`T.elem` "-<>=/|")

keywords :: [Text]
keywords =
  [ "if", "else", "match", "handle", "handler", "mask", "return", "finally", "let", "fn", "as"
  , "type", "module", "signature", "implicit", "instance", "open", "include", "extern", "effect"
  , "protocol", "infix", "infixl", "infixr"
  ]

-- | Identifier tokens outside comments, strings and character literals, without keywords.
identifiers :: Text -> Set.Set Text
identifiers = (`Set.difference` Set.fromList ("_" : keywords)) . go Set.empty
 where
  go acc t = case T.uncons t of
    Nothing -> acc
    Just (x, r)
      | isLetter x || x == '_' -> let (w, r') = T.span identChar t in go (Set.insert w acc) r'
      | x == '"' -> go acc (T.drop 1 (T.dropWhile (/= '"') r))
      | x == '\'', Just (_, r') <- T.uncons r, "'" `T.isPrefixOf` r' -> go acc (T.drop 1 r')
      | "{-" `T.isPrefixOf` t -> go acc (block (1 :: Int) (T.drop 2 t))
      | opChar x ->
          let (o, r') = T.span opChar t
          in go acc (if T.length o >= 2 && T.all (== '-') o then T.dropWhile (/= '\n') r' else r')
      | otherwise -> go acc r
  block 0 t = t
  block n t
    | "{-" `T.isPrefixOf` t = block (n + 1) (T.drop 2 t)
    | "-}" `T.isPrefixOf` t = block (n - 1) (T.drop 2 t)
    | T.null t = t
    | otherwise = block n (T.drop 1 t)
  opChar x = x `T.elem` "!#$%&*+-/:<=>?@^|~" || ('\x2190' <= x && x <= '\x22FF')

identChar :: Char -> Bool
identChar x = isAlphaNum x || x == '_' || x == '\''

-- | @{"ms": n}@: wait, then answer @null@; for trying out @$/cancelRequest@.
sleep :: RequestHandler
sleep _ _ p = case parseEither (withObject "SleepParams" (.: "ms")) p of
  Left e -> pure (Left (invalidParams (T.pack e)))
  Right ms -> do
    logDebug ("sleeping " <> T.pack (show ms) <> " ms")
    liftIO (threadDelay (ms * 1000))
    pure (Right Null)
