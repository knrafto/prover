{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
module Prover.Parser
    ( module_
    )
where

import           Control.Monad

import           Control.Monad.Combinators.Expr
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

import           Prover.Syntax.Position
import           Prover.Syntax.Concrete

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

isWordChar :: Char -> Bool
isWordChar c = c `notElem` (" \t\r\n\f\v(),." :: [Char])

reservedWord :: Text -> Parser Range
reservedWord w = lexeme . try $ do
    s <- getOffset
    _ <- string w
    notFollowedBy (satisfy isWordChar)
    Range s <$> getOffset

name :: Parser Name
name = lexeme . try $ do
    s <- getOffset
    w <- takeWhile1P (Just "word character") isWordChar
    when (w `elem` reservedWords) $ fail
        (  "keyword "
        ++ Text.unpack w
        ++ " is reserved and cgetRangeot be used as a name"
        )
    e <- getOffset
    return (Name (Range s e) w)
  where
    reservedWords :: [Text]
    reservedWords =
        [ "_"
        , ":"
        , "≡"
        , "="
        , "Σ"
        , "Π"
        , "λ"
        , "→"
        , "×"
        , "Type"
        , "define"
        , "assume"
        , "prove"
        ]

symbol :: Char -> Parser Range
symbol c = lexeme $ do
    s <- getOffset
    _ <- char c
    Range s <$> getOffset

param :: Parser Param
param = (,) <$> name <*> optional (reservedWord ":" *> expr)

atom :: Parser Expr
atom = id_ <|> hole <|> type_ <|> parens <|> sigma <|> pi_ <|> lam
  where
    id_   = Id <$> name
    hole  = Hole <$> reservedWord "_"
    type_ = Type <$> reservedWord "Type"
    parens = do
        _ <- symbol '('
        e <- expr
        _ <- symbol ')'
        return e
    pi_ = do
        s <- reservedWord "Π"
        p <- param
        _ <- symbol '.'
        e <- expr
        return (Pi (rangeSpan s (getRange e)) p e)
    lam = do
        s <- reservedWord "λ"
        p <- param
        _ <- symbol '.'
        e <- expr
        return (Lam (rangeSpan s (getRange e)) p e)
    sigma = do
        s <- reservedWord "Σ"
        p <- param
        _ <- symbol '.'
        e <- expr
        return (Sigma (rangeSpan s (getRange e)) p e)

apps :: Parser Expr
apps = do
    x <- atom
    rest x
  where
    rest x = app x <|> return x

    app x = do
        arg <- atom
        rest (App (rangeSpan (getRange x) (getRange arg)) x arg)

expr :: Parser Expr
expr = makeExprParser
    apps
    [ [InfixR (binop Times  <$ reservedWord "×")]
    , [InfixN (binop Equals <$ reservedWord "=")]
    , [InfixR (binop Arrow  <$ reservedWord "→")]
    , [InfixR (binop Pair   <$ symbol       ',')]
    ]
    where binop c e1 e2 = c (rangeSpan (getRange e1) (getRange e2)) e1 e2

define :: Parser Decl
define =
    Define
        <$  reservedWord "define"
        <*> name
        <*> optional (reservedWord ":" *> expr)
        <*  reservedWord "≡"
        <*> expr

assume :: Parser Decl
assume =
    Assume <$ reservedWord "assume" <*> name <* reservedWord ":" <*> expr

decl :: Parser Decl
decl = define <|> assume

module_ :: Parser Module
module_ = Module <$ sc <*> many decl <* eof
