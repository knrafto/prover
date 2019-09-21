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
isWhitespaceChar c = c `elem` " \t\r\n#"

isPunctuationChar :: Char -> Bool
isPunctuationChar c = c `elem` "(),"

isWordChar :: Char -> Bool
isWordChar c = not (isWhitespaceChar c || isPunctuationChar c)

isTopLevel :: Text -> Bool
isTopLevel t = not (Text.null t || isWhitespaceChar (Text.head t))

groupIndentedLines :: [Text] -> [[Text]]
groupIndentedLines = go []
  where
    go currentGroup [] = [reverse currentGroup]
    go currentGroup (l:ls)
        | isTopLevel l = reverse currentGroup : go [l] ls
        | otherwise = go (l:currentGroup) ls

data Token
    = Whitespace Char
    | Comment Text
    | Word Text
    | LParen
    | RParen
    | Comma
    deriving (Show)

tokenizeLine :: Text -> [Token]
tokenizeLine t
    | Text.null t = []
    | otherwise = case Text.head t of
        '(' -> LParen : tokenizeLine (Text.tail t)
        ')' -> RParen : tokenizeLine (Text.tail t)
        ',' -> Comma : tokenizeLine (Text.tail t)
        '#' -> [Comment t]
        c | isWhitespaceChar c -> Whitespace c : tokenizeLine (Text.tail t)
          | otherwise ->
                let (token, rest) = Text.span isWordChar t
                in Word token : tokenizeLine rest
