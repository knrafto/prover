{-# LANGUAGE OverloadedStrings #-}
module Token where

import           Control.Monad

import           Data.Text                      ( Text )
import           Data.Text                     as Text
import           Data.Void
import           Text.Megaparsec         hiding ( Token
                                                , token
                                                )
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

import           Location

type Parser = Parsec Void Text

data Token
    = Identifier Ident
    | ReservedWord Ident
    | Symbol Ident
    deriving (Eq, Show)

spaceChars :: [Char]
spaceChars = " \t\r\n\f\v"

-- TODO: allow nested comments (in TextMate grammar, too)
sc :: Parser ()
sc = L.space spaces (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")
    where spaces = void $ takeWhile1P (Just "white space") (`elem` spaceChars)

symbolChars :: [Char]
symbolChars = "(),"

reservedWords :: [Text]
reservedWords =
    [ "_"
    , ":"
    , ":="
    , "Σ"
    , "Π"
    , "λ"
    , "="
    , "×"
    , "→"
    , "Type"
    , "define"
    , "assume"
    , "prove"
    ]

isWordChar :: Char -> Bool
isWordChar c = c `notElem` (spaceChars ++ symbolChars)

located :: Parser a -> Parser (Located a)
located m = do
    s <- getOffset
    a <- m
    e <- getOffset
    return (L (Range s e) a)

symbol :: Parser Ident
symbol = located $ choice [ string (Text.pack [c]) | c <- symbolChars ]

reservedWord :: Parser Ident
reservedWord = located $ choice
    [ try (string w <* notFollowedBy (satisfy isWordChar))
    | w <- reservedWords
    ]

identifier :: Parser Ident
identifier = located $ takeWhile1P (Just "word character") isWordChar

token :: Parser Token
token = Symbol <$> symbol
    <|> ReservedWord <$> reservedWord
    <|> Identifier <$> identifier

tokenize :: Text -> [Token]
tokenize input = case parse (sc *> many (token <* sc) <* eof) "" input of
    Left  e  -> error ("parse error when tokenizing:\n" ++ errorBundlePretty e)
    Right xs -> xs
