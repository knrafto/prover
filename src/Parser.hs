{-# LANGUAGE OverloadedStrings #-}
module Parser (statements) where

import Control.Monad

import Data.Text (Text)
import qualified Data.Text as Text
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

import Syntax

type Parser = Parsec Void Text

lineComment :: Parser ()
lineComment = L.skipLineComment "#"

sc :: Parser ()
sc = L.space space1 lineComment empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

isWordChar :: Char -> Bool
isWordChar c = c `notElem` (" \t\r\n\f\v#()," :: [Char])

reservedWord :: Text -> Parser ()
reservedWord w =
    lexeme . try $ (string w *> notFollowedBy (satisfy isWordChar))

identifier :: Parser Text
identifier = lexeme . try $ do
    w <- takeWhile1P (Just "word character") isWordChar
    when (w `elem` reservedWords) $ fail
        (  "keyword "
        ++ Text.unpack w
        ++ " is reserved and cannot be used as an identifier"
        )
    return w
  where
    reservedWords :: [Text]
    reservedWords = [":", ":=", "=", "Σ", "Π", "λ", "→", ":assume"]

symbol :: Char -> Parser ()
symbol c = lexeme (void $ char c)

parens :: Parser a -> Parser a
parens = between (symbol '(') (symbol ')')

atom :: Parser Expr
atom = Var <$> identifier
   <|> parens expr
   <|> Sigma <$ reservedWord "Σ" <*> params <*> expr
   <|> Pi <$ reservedWord "Π" <*> params <*> expr
   <|> Lambda <$ reservedWord "λ" <*> params <*> expr

expr :: Parser Expr
expr = do
    x <- atom
    rest x
  where
    rest x = apply x <|> arrow x <|> return x

    apply x = do
        args <- parens $ expr `sepBy1` symbol ','
        rest (Apply x args)

    arrow x = do
        reservedWord "→"
        y <- expr
        return (Arrow x y)

params :: Parser Params
params = parens $ param `sepBy1` symbol ','
    where param = (,) <$> identifier <* reservedWord ":" <*> expr

assume :: Parser Statement
assume = do
    reservedWord ":assume"
    name <- identifier
    reservedWord ":"
    t <- expr
    return (Assume name t)

define :: Parser Statement
define = do
    name <- identifier
    ps   <- params
    reservedWord ":"
    t <- expr
    reservedWord ":="
    b <- expr
    return (Define name ps t b)

statement :: Parser Statement
statement = L.nonIndented sc $ assume <|> define

statements :: Parser [Statement]
statements = many statement <* eof