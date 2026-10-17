{-# LANGUAGE OverloadedStrings #-}

-- | JSON-RPC 2.0 messages and the LSP @Content-Length@ framing.
module CaraML.Lsp.JsonRpc
  ( Id (..)
  , Message (..)
  , ResponseError (..)
  , parseError
  , invalidRequest
  , methodNotFound
  , invalidParams
  , internalError
  , serverNotInitialized
  , requestCancelled
  , decodeMessage
  , readFrame
  , frame
  , responseFrame
  , notificationFrame
  , requestFrame
  ) where

import Control.Applicative ((<|>))
import Control.Monad ((>=>))
import Data.Aeson (FromJSON (..), ToJSON (..), Value (..), object, withObject, (.!=), (.:), (.:?), (.=))
import Data.Aeson.Types (Parser, parseEither)
import Data.ByteString.Builder (Builder, byteString, intDec, string7)
import Data.Char (toLower)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import System.IO (Handle)
import System.IO.Error (catchIOError, isEOFError)

import qualified Data.Aeson as Json
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8

data Id = IdInt !Int | IdText !Text
  deriving (Eq, Ord, Show)

instance FromJSON Id where
  parseJSON v@(Number _) = IdInt <$> parseJSON v
  parseJSON (String s) = pure (IdText s)
  parseJSON _ = fail "id: expected an integer or a string"

instance ToJSON Id where
  toJSON (IdInt i) = toJSON i
  toJSON (IdText s) = toJSON s

data Message
  = Request !Id !Text !Value
  | Notification !Text !Value
  | Response !Id !(Either ResponseError Value)

data ResponseError = ResponseError { errCode :: !Int, errMessage :: !Text }
  deriving (Show)

instance FromJSON ResponseError where
  parseJSON = withObject "ResponseError" $ \o -> ResponseError <$> o .: "code" <*> o .: "message"

instance ToJSON ResponseError where
  toJSON (ResponseError c m) = object ["code" .= c, "message" .= m]

parseError, invalidRequest, methodNotFound, invalidParams, internalError :: Text -> ResponseError
parseError     = ResponseError (-32700)
invalidRequest = ResponseError (-32600)
methodNotFound = ResponseError (-32601)
invalidParams  = ResponseError (-32602)
internalError  = ResponseError (-32603)

serverNotInitialized, requestCancelled :: ResponseError
serverNotInitialized = ResponseError (-32002) "server not initialized"
requestCancelled     = ResponseError (-32800) "request cancelled"

decodeMessage :: BS.ByteString -> Either String Message
decodeMessage = Json.eitherDecodeStrict >=> parseEither message

message :: Value -> Parser Message
message = withObject "message" $ \o -> do
  mid <- o .:? "id"
  mm  <- o .:? "method"
  case (mid, mm) of
    (Just i, Just m)  -> Request i m <$> o .:? "params" .!= Null
    (Nothing, Just m) -> Notification m <$> o .:? "params" .!= Null
    (Just i, Nothing) -> Response i <$> (Left <$> o .: "error" <|> Right <$> o .:? "result" .!= Null)
    (Nothing, Nothing) -> fail "neither id nor method"

-- | The next frame's body, 'Nothing' at end of input.
readFrame :: Handle -> IO (Maybe BS.ByteString)
readFrame h = headers Nothing `catchIOError` \e -> if isEOFError e then pure Nothing else ioError e
 where
  headers len = do
    l <- (\l -> fromMaybe l (BS8.stripSuffix "\r" l)) <$> BS8.hGetLine h
    if BS.null l
      then maybe (headers Nothing) body len
      else headers (contentLength l <|> len)

  body n = do
    b <- BS.hGet h n
    pure (if BS.length b == n then Just b else Nothing)

  contentLength l = case BS8.break (== ':') l of
    (k, v) | BS8.map toLower k == "content-length"
           , Just (n, rest) <- BS8.readInt (BS8.strip (BS.drop 1 v))
           , BS.null rest -> Just n
    _ -> Nothing

frame :: BS.ByteString -> Builder
frame b = string7 "Content-Length: " <> intDec (BS.length b) <> string7 "\r\n\r\n" <> byteString b

-- | A response to @Nothing@ carries @"id": null@ (for a message whose id could not be read).
responseFrame :: Maybe Id -> Either ResponseError Value -> BS.ByteString
responseFrame i r = encode $
  ["id" .= i] ++ either (\e -> ["error" .= e]) (\x -> ["result" .= x]) r

notificationFrame :: Text -> Value -> BS.ByteString
notificationFrame m p = encode ["method" .= m, "params" .= p]

requestFrame :: Id -> Text -> Value -> BS.ByteString
requestFrame i m p = encode ["id" .= i, "method" .= m, "params" .= p]

encode :: [(Json.Key, Value)] -> BS.ByteString
encode kvs = BS.toStrict (Json.encode (object (("jsonrpc" .= ("2.0" :: Text)) : kvs)))
