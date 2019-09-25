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
isWordChar c = c `notElem` (" \t\r\n\f\v#(),." :: [Char])

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
    reservedWords = [":", ":=", "Σ", "Π", "λ", "→", "Type", ":assume", ":prove"]

symbol :: Char -> Parser ()
symbol c = lexeme (void $ char c)

parens :: Parser a -> Parser a
parens = between (symbol '(') (symbol ')')

atom :: Parser Expr
atom = Var <$> identifier
   <|> parens expr
   <|> Universe <$ reservedWord "Type"
   <|> Sigma <$ reservedWord "Σ" <*> params <* symbol '.' <*> expr
   <|> Pi <$ reservedWord "Π" <*> params <* symbol '.' <*> expr
   <|> Lambda <$ reservedWord "λ" <*> params <* symbol '.' <*> expr

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

define :: Parser Statement
define = Define
    <$> identifier
    <*> params
    <* reservedWord ":"
    <*> expr
    <* reservedWord ":="
    <*> expr

assume :: Parser Statement
assume = Assume
    <$ reservedWord ":assume"
    <*> identifier
    <* reservedWord ":"
    <*> expr

prove :: Parser Statement
prove = Prove
    <$ reservedWord ":assume"
    <*> expr

statement :: Parser Statement
statement = L.nonIndented sc $ assume <|> define

statements :: Parser [Statement]
statements = many statement <* eof