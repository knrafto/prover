module Lib where

import Data.Text (Text)
import qualified Data.Text as Text

isWhitespaceChar :: Char -> Bool
isWhitespaceChar c = c `elem` " \t\r\n"

isPunctuationChar :: Char -> Bool
isPunctuationChar c = c `elem` "(),"

isWordChar :: Char -> Bool
isWordChar c = not (isWhitespaceChar c || isPunctuationChar c || c == '#')

data Token
    = Whitespace Char
    | Comment Text
    | Word Text
    | LParen
    | RParen
    | Comma
    deriving (Show)

tokenize :: Text -> [Token]
tokenize t
    | Text.null t = []
    | otherwise = case Text.head t of
        '(' -> LParen : tokenize (Text.tail t)
        ')' -> RParen : tokenize (Text.tail t)
        ',' -> Comma : tokenize (Text.tail t)
        '#' -> case Text.findIndex (== '\n') t of
            Nothing -> [Comment t]
            Just i ->
                let (comment, rest) = Text.splitAt (i + 1) t
                in Comment comment : tokenize rest
        c | isWhitespaceChar c -> Whitespace c : tokenize (Text.tail t)
          | otherwise ->
                let (token, rest) = Text.span isWordChar t
                in Word token : tokenize rest
