{-# LANGUAGE OverloadedStrings #-}
module Token where

import           Control.Monad

import           Data.Text                     ( Text )
import           Data.Text as Text
import           Data.Void
import           Text.Megaparsec hiding (Token, token)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

import Location

type Parser = Parsec Void Text

data Token
    = Identifier Text
    | ReservedWord Text
    | Symbol Char
    deriving (Eq)

instance Show Token where
    show (Identifier t) = Text.unpack t
    show (ReservedWord t) = Text.unpack t
    show (Symbol c) = [c]

type LToken = Located Token

spaceChars :: [Char]
spaceChars = " \t\r\n\f\v"

-- TODO: allow nested comments (in TextMate grammar, too)
sc :: Parser ()
sc = L.space spaces (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")
  where
    spaces = void $ takeWhile1P (Just "white space") (`elem` spaceChars)

symbolChars :: [Char]
symbolChars = "(),"

reservedWords :: [Text]
reservedWords =
    [ "_", ":", ":=", "Σ", "Π", "λ", "=", "×", "→", "Type"
    , "define", "assume", "prove"
    ]

isWordChar :: Char -> Bool
isWordChar c = c `notElem` (spaceChars ++ symbolChars)

symbol :: Parser Token
symbol = Symbol <$> choice [char c | c <- symbolChars]

reservedWord :: Parser Token
reservedWord = ReservedWord <$> choice
    [try (string w <* notFollowedBy (satisfy isWordChar)) | w <- reservedWords]

identifier :: Parser Token
identifier = Identifier <$> takeWhile1P (Just "word character") isWordChar

token :: Parser LToken
token = do
    s <- getOffset
    t <- symbol <|> reservedWord <|> identifier
    e <- getOffset
    sc
    return (L (SrcSpan s e) t)

tokenize :: Text -> [LToken]
tokenize input = case parse (sc *> many token <* eof) "" input of
    Left e -> error ("parse error when tokenizing:\n" ++ errorBundlePretty e)
    Right xs -> xs