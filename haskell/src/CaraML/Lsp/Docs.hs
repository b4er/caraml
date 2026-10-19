-- | Open documents as UTF-16-addressable ropes, so an incremental edit costs O(log n).
module CaraML.Lsp.Docs
  ( Uri
  , Doc (..)
  , Docs
  , Position (..)
  , DidOpen (..)
  , DidChange (..)
  , DidClose (..)
  , At (..)
  , applyChanges
  , lineAt
  , position
  , splitAtPosition
  ) where

import Control.Monad (foldM)
import Data.Aeson (FromJSON (..), Value, object, withObject, (.:), (.:?), (.=))
import Data.Aeson.Types (Parser)
import Data.Map.Strict (Map)
import Data.Text (Text)
import Data.Text.Lines (Position (..))
import Data.Text.Utf16.Rope.Mixed (Rope)

import qualified Data.Text.Utf16.Rope.Mixed as Rope

type Uri = Text

data Doc = Doc { version :: !Int, text :: !Rope }

type Docs = Map Uri Doc

data DidOpen = DidOpen !Uri !Doc

data DidChange = DidChange !Uri !Int ![Change]

newtype DidClose = DidClose Uri

-- | @textDocument@ and @position@ of a positional request.
data At = At !Uri !Position

data Change = Change !(Maybe (Position, Position)) !Text

instance FromJSON DidOpen where
  parseJSON = withObject "DidOpenTextDocumentParams" $ \o -> do
    td <- o .: "textDocument"
    DidOpen <$> td .: "uri" <*> (Doc <$> td .: "version" <*> (Rope.fromText <$> td .: "text"))

instance FromJSON DidChange where
  parseJSON = withObject "DidChangeTextDocumentParams" $ \o -> do
    td <- o .: "textDocument"
    DidChange <$> td .: "uri" <*> td .: "version" <*> o .: "contentChanges"

instance FromJSON DidClose where
  parseJSON = withObject "DidCloseTextDocumentParams" $ \o ->
    DidClose <$> (o .: "textDocument" >>= (.: "uri"))

instance FromJSON At where
  parseJSON = withObject "TextDocumentPositionParams" $ \o ->
    At <$> (o .: "textDocument" >>= (.: "uri")) <*> (o .: "position" >>= pos)

instance FromJSON Change where
  parseJSON = withObject "TextDocumentContentChangeEvent" $ \o -> do
    r <- o .:? "range"
    Change <$> traverse range r <*> o .: "text"
   where
    range = withObject "Range" $ \o -> (,) <$> (o .: "start" >>= pos) <*> (o .: "end" >>= pos)

pos :: Value -> Parser Position
pos = withObject "Position" $ \o -> Position <$> o .: "line" <*> o .: "character"

position :: Position -> Value
position (Position l c) = object ["line" .= l, "character" .= c]

-- | Apply a didChange batch in order; 'Left' when a range does not fit the text.
applyChanges :: Rope -> [Change] -> Either String Rope
applyChanges = foldM apply
 where
  apply _ (Change Nothing t) = Right (Rope.fromText t)
  apply r (Change (Just (s, e)) t)
    | (posLine e, posColumn e) < (posLine s, posColumn s) = Left "range ends before it starts"
    | otherwise = do
        (pre, _) <- splitAt' s r
        (_, post) <- splitAt' e r
        pure (pre <> Rope.fromText t <> post)
  splitAt' p = maybe (Left "position splits a surrogate pair") Right . splitAtPosition p

-- | Split at a UTF-16 position, clamping the column to the line as LSP requires
-- ('Rope.utf16SplitAtPosition' would run on into the next line).
splitAtPosition :: Position -> Rope -> Maybe (Rope, Rope)
splitAtPosition (Position l c) r = do
  let (pre, rest) = Rope.splitAtLine l r
  (a, b) <- Rope.utf16SplitAt (min c (Rope.utf16Length (lineOf rest))) rest
  pure (pre <> a, b)

-- | Line @l@ without its terminator.
lineAt :: Word -> Rope -> Rope
lineAt l = lineOf . snd . Rope.splitAtLine l

lineOf :: Rope -> Rope
lineOf r = case Rope.utf16SplitAt (Rope.utf16Length line - 1) line of
  Just (x, nl) | Rope.toText nl == "\n" -> x
  _ -> line
 where
  line = fst (Rope.splitAtLine 1 r)
