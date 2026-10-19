module CaraML.Lsp.Handlers (handlers) where

import Control.Concurrent (threadDelay)
import Control.Monad.Reader (liftIO)
import Data.Aeson (Value (..), object, withObject, (.:), (.=))
import Data.Aeson.Types (parseEither)
import Data.Char (isAsciiLower, isAsciiUpper, isUpper)
import Data.Maybe (listToMaybe)
import Data.Text (Text)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Utf16.Rope.Mixed as Rope

import CaraML.Cli
import CaraML.Language (Err (..), Span (..), boundNames, isIdentChar, keywords, parseModule, typecheck)
import CaraML.Lsp.Abbreviations
import CaraML.Lsp.Docs
import CaraML.Lsp.JsonRpc
import CaraML.Lsp.Server

handlers :: Handlers
handlers = Handlers
  { capabilities =
      [ "hoverProvider" .= True
      , "completionProvider" .= object ["triggerCharacters" .= ["\\" :: Text]]
      ]
  , requests = Map.fromList
      [ ("textDocument/hover", hover)
      , ("textDocument/completion", completion)
      , ("caraml/sleep", sleep)
      ]
  , notifications = Map.empty
  , diagnose = \_ d -> pure (diagnostics d)
  }

-- | The errors of parsing and checking a document.
diagnostics :: Doc -> [Value]
diagnostics d = case parseModule (Rope.toText d.text) >>= typecheck of
  Right () -> []
  Left e -> [ object
                [ "range" .= range e.span, "severity" .= (1 :: Int)
                , "source" .= ("caraml" :: Text), "message" .= e.msg ] ]
 where
  range = \case
    Nothing -> object ["start" .= origin, "end" .= origin]
    Just sp ->
      let l = fromIntegral (sp.line - 1)
          at c = position (Position l (utf16 l c))
      in object ["start" .= at (sp.col - 1), "end" .= at (sp.col - 1 + sp.len)]
  origin = position (Position 0 0)
  -- Span columns count characters, LSP columns UTF-16 code units
  utf16 l c = Rope.utf16Length (Rope.fromText (T.take c (Rope.toText (lineAt l d.text))))

-- | The identifier under the cursor and the document version.
hover :: RequestHandler
hover _ docs p = withParams p $ \(At uri (Position l c)) ->
  pure . Right $ case Map.lookup uri docs of
    Nothing -> Null
    Just d -> object
      [ "contents" .= object
          [ "kind" .= ("markdown" :: Text)
          , "value" .= ("`" <> word (lineAt l d.text) c <> "` at " <> T.pack (show l) <> ":"
                         <> T.pack (show c) <> ", version " <> T.pack (show d.version))
          ]
      ]
 where
  word line c = case splitAtPosition (Position 0 c) line of
    Nothing -> ""
    Just (a, b) -> T.takeWhileEnd ident (Rope.toText a) <> T.takeWhile ident (Rope.toText b)
  ident = isIdentChar

-- | After @\\name@ the abbreviations, replacing it; otherwise the keywords and the
-- names the document binds at the top level (none while it does not parse). No
-- scopes and no types yet.
completion :: RequestHandler
completion _ docs p = withParams p $ \(At uri (Position l c)) ->
  pure . Right $ case Map.lookup uri docs of
    Nothing -> Null
    Just d ->
      let before = maybe mempty fst (splitAtPosition (Position 0 c) (lineAt l d.text))
          end = Rope.utf16Length before
          typed = Rope.toText before
          items = case pendingAbbreviation typed of
            Just n ->
              let start = Position l (end - fromIntegral (T.length n) - 1)
              in map (abbreviation start (Position l end)) abbreviations
            Nothing -> map (item 14 "keyword") keywords
              ++ [ item (if isUpper (T.head w) then 9 else 6) "in this document" w
                 | w <- either (const []) (Set.toList . boundNames) (parseModule (Rope.toText d.text))
                 , w /= T.takeWhileEnd isIdentChar typed
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

-- | @{"ms": n}@: wait, then answer @null@; for trying out @$/cancelRequest@.
sleep :: RequestHandler
sleep _ _ p = case parseEither (withObject "SleepParams" (.: "ms")) p of
  Left e -> pure (Left (invalidParams (T.pack e)))
  Right ms -> do
    logDebug ("sleeping " <> T.pack (show ms) <> " ms")
    liftIO (threadDelay (ms * 1000))
    pure (Right Null)
