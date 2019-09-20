module Lib where

import Data.Text (Text)
import qualified Data.Text as Text

-- | Break a string into lines, preserving newlines.
splitLines :: Text -> [Text]
splitLines ps
    | Text.null ps = []
    | otherwise = case Text.findIndex (== '\n') ps of
        Nothing -> [ps]
        Just i -> let (h , t) = Text.splitAt (i + 1) ps in h : splitLines t
