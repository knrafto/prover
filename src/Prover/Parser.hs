{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
module Prover.Parser ( parseModule ) where

import Control.Monad

import Control.Monad.Combinators.Expr
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

import Prover.Syntax.Position
import Prover.Syntax.Concrete

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

isWordChar :: Char -> Bool
isWordChar c = c `notElem` (" \t\r\n\f\v(),." :: [Char])

getPosition :: Parser Position
getPosition = do
    SourcePos _ l c <- getSourcePos
    offset <- getOffset
    return (Position (unPos l) (unPos c) offset)

reservedWord :: Text -> Parser Range
reservedWord w = lexeme . try $ do
    s <- getPosition
    _ <- string w
    notFollowedBy (satisfy isWordChar)
    Range s <$> getPosition

name :: Parser Name
name = lexeme . try $ do
    s <- getPosition
    w <- takeWhile1P (Just "word character") isWordChar
    when (w `elem` reservedWords) $ fail
        (  "keyword "
        ++ T.unpack w
        ++ " is reserved and cgetRangeot be used as a name"
        )
    e <- getPosition
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
        , "axiom"
        ]

symbol :: Char -> Parser Range
symbol c = lexeme $ do
    s <- getPosition
    _ <- char c
    Range s <$> getPosition

binderParam :: Parser Param
binderParam = (,) <$> name <*> optional (reservedWord ":" *> expr)

telescopeParam :: Parser Param
telescopeParam = explicitParam <|> (\n -> (n, Nothing)) <$> name
  where
    explicitParam = (,) <$ symbol '(' <*> name <* reservedWord ":" <*> (Just <$> expr) <* symbol ')'

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
        p <- binderParam
        _ <- symbol '.'
        e <- expr
        return (Pi (rangeSpan s (getRange e)) p e)
    lam = do
        s <- reservedWord "λ"
        p <- binderParam
        _ <- symbol '.'
        e <- expr
        return (Lam (rangeSpan s (getRange e)) p e)
    sigma = do
        s <- reservedWord "Σ"
        p <- binderParam
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
        <*> many telescopeParam
        <*> optional (reservedWord ":" *> expr)
        <*  reservedWord "≡"
        <*> expr

axiom :: Parser Decl
axiom =
    Assume
        <$  reservedWord "axiom"
        <*> name
        <*> many telescopeParam
        <*  reservedWord ":"
        <*> expr

decl :: Parser Decl
decl = define <|> axiom

module_ :: Parser Module
module_ = Module <$ sc <*> many decl <* eof

parseModule :: FilePath -> Text -> Either String Module
parseModule path input = case parse module_ path input of
    Left  e -> Left (errorBundlePretty e)
    Right m -> Right m
