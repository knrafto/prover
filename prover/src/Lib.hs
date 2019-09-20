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

isWhitespaceChar :: Char -> Bool
isWhitespaceChar c = c == ' ' || c == '\t' || c == '\r' || c == '\n'

isTopLevel :: Text -> Bool
isTopLevel t = not (Text.null t) && isTopLevelChar (Text.head t)
  where
    isTopLevelChar c = not (isWhitespaceChar c || c == '#')

groupIndentedLines :: [Text] -> [[Text]]
groupIndentedLines = go []
  where
    go currentGroup [] = [reverse currentGroup]
    go currentGroup (l:ls)
        | isTopLevel l = reverse currentGroup : go [l] ls
        | otherwise = go (l:currentGroup) ls
