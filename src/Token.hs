{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- Tokenization.
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

data TokenType
    = Identifier
    | LParen
    | RParen
    | Comma
    | Dot
    | Underscore
    | Colon
    | DefEquals
    | Sigma
    | Pi
    | Lambda
    | Equals
    | Times
    | Arrow
    | Type
    | Define
    | Assume
    | Prove
    deriving (Eq, Show)

data Token = Token
    { tokenKind :: TokenType
    , tokenIdent :: Ident
    }
    deriving (Eq, Show)

type Parser = Parsec Void Text

spaceChars :: [Char]
spaceChars = " \t\r\n\f\v"

symbolChars :: [Char]
symbolChars = "(),."

sc :: Parser ()
sc = L.space spaces (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")
    where spaces = void $ takeWhile1P (Just "white space") (`elem` spaceChars)

isWordChar :: Char -> Bool
isWordChar c = c `notElem` (spaceChars ++ symbolChars)

ident :: Parser Text -> Parser Ident
ident m = do
    s <- getOffset
    a <- m
    e <- getOffset
    return (Ident (Range s e) a)

symbol :: Char -> Parser Ident
symbol c = ident $ string (Text.pack [c])

reservedWord :: Text -> Parser Ident
reservedWord w = ident $ try (string w <* notFollowedBy (satisfy isWordChar))

identifier :: Parser Ident
identifier = ident $ takeWhile1P (Just "word character") isWordChar

token :: Parser Token
token = choice
    [ Token LParen      <$> symbol '('
    , Token RParen      <$> symbol ')'
    , Token Comma       <$> symbol ','
    , Token Dot         <$> symbol '.'
    , Token Underscore  <$> reservedWord "_"
    , Token Colon       <$> reservedWord ":"
    , Token DefEquals   <$> reservedWord "≡"
    , Token Sigma       <$> reservedWord "Σ"
    , Token Pi          <$> reservedWord "Π"
    , Token Lambda      <$> reservedWord "λ"
    , Token Equals      <$> reservedWord "="
    , Token Times       <$> reservedWord "×"
    , Token Arrow       <$> reservedWord "→"
    , Token Type        <$> reservedWord "Type"
    , Token Define      <$> reservedWord "define"
    , Token Assume      <$> reservedWord "assume"
    , Token Prove       <$> reservedWord "prove"
    , Token Identifier  <$> identifier
    ]

tokenize :: Text -> [Token]
tokenize input = case parse (sc *> many (token <* sc) <* eof) "" input of
    Left  e  -> error ("parse error when tokenizing:\n" ++ errorBundlePretty e)
    Right xs -> xs
