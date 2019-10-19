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
    reservedWords = ["_", ":", ":=", "Σ", "Π", "λ", "→", "Type", ":assume", ":prove"]

symbol :: Char -> Parser ()
symbol c = lexeme (void $ char c)

atom :: Parser Expr
atom = Hole <$ reservedWord "_"
   <|> Var <$> identifier
   <|> symbol '(' *> expr <* symbol ')'
   <|> Universe <$ reservedWord "Type"
   <|> Sigma <$ reservedWord "Σ"
        <* symbol '(' <*> identifier <* reservedWord ":" <*> expr <* symbol ')'
        <* symbol '.' <*> expr
   <|> Pi <$ reservedWord "Π"
        <* symbol '(' <*> identifier <* reservedWord ":" <*> expr <* symbol ')'
        <* symbol '.' <*> expr
   <|> Lam <$ reservedWord "λ"
        <* symbol '(' <*> identifier <* reservedWord ":" <*> expr <* symbol ')'
        <* symbol '.' <*> expr

expr :: Parser Expr
expr = do
    x <- atom
    rest x
  where
    rest x = apply x <|> arrow x <|> return x

    apply x = do
        symbol '('
        args <- expr `sepBy1` symbol ','
        symbol ')'
        rest (App x args)

    arrow x = do
        reservedWord "→"
        y <- expr
        return (Arrow x y)

define :: Parser Statement
define = Define <$> identifier <*> optional (reservedWord ":" *> expr) <* reservedWord ":=" <*> expr

assume :: Parser Statement
assume = Assume <$ reservedWord ":assume" <*> identifier <* reservedWord ":" <*> expr

prove :: Parser Statement
prove = Prove <$ reservedWord ":prove" <*> expr

statement :: Parser Statement
statement = L.nonIndented sc $ assume <|> prove <|> define

statements :: Parser [Statement]
statements = many statement <* eof