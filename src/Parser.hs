{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
module Parser
    ( P
    , statements
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

import           Location
import           Syntax

-- Tag for parsed syntax trees, which have been decorated with locations.
data P
type instance Id P = Ident
type instance Ann P = Range

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

isWordChar :: Char -> Bool
isWordChar c = c `notElem` (" \t\r\n\f\v()," :: [Char])

reservedWord :: Text -> Parser Range
reservedWord w = lexeme . try $ do
    s <- getOffset
    _ <- string w
    notFollowedBy (satisfy isWordChar)
    Range s <$> getOffset

identifier :: Parser (Id P)
identifier = lexeme . try $ do
    s <- getOffset
    w <- takeWhile1P (Just "word character") isWordChar
    when (w `elem` reservedWords) $ fail
        (  "keyword "
        ++ Text.unpack w
        ++ " is reserved and cannot be used as an identifier"
        )
    e <- getOffset
    return (L (Range s e) w)
  where
    reservedWords :: [Text]
    reservedWords =
        [ "_"
        , ":"
        , ":="
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

params :: Parser [Param P]
params = symbol '(' *> param `sepBy1` symbol ',' <* symbol ')'
    where param = (,) <$> identifier <* reservedWord ":" <*> expr

atom :: Parser (Expr P)
atom = var <|> hole <|> type_ <|> tuple <|> sigma <|> pi_ <|> lam
  where
    var = do
        i <- identifier
        return (Var (location i) i)
    hole  = Hole <$> reservedWord "_"
    type_ = Type <$> reservedWord "Type"
    tuple = do
        s  <- symbol '('
        es <- expr `sepBy1` symbol ','
        e  <- symbol ')'
        return (Tuple (spanRange s e) es)
    sigma = do
        s <- reservedWord "Σ"
        p <- params
        e <- expr
        return (Sigma (spanRange s (ann e)) p e)
    pi_ = do
        s <- reservedWord "Π"
        p <- params
        e <- expr
        return (Pi (spanRange s (ann e)) p e)
    lam = do
        s <- reservedWord "λ"
        p <- params
        e <- expr
        return (Lambda (spanRange s (ann e)) p e)

apps :: Parser (Expr P)
apps = do
    x <- atom
    rest x
  where
    rest x = app x <|> return x

    app x = do
        _    <- symbol '('
        args <- expr `sepBy1` symbol ','
        e    <- symbol ')'
        rest (App (spanRange (ann x) e) x args)

expr :: Parser (Expr P)
expr = makeExprParser
    apps
    [ [InfixR (binop Times <$ reservedWord "×")]
    , [InfixN (binop Equal <$ reservedWord "=")]
    , [InfixR (binop Arrow <$ reservedWord "→")]
    ]
    where binop c e1 e2 = c (spanRange (ann e1) (ann e2)) e1 e2

define :: Parser (Statement P)
define =
    Define
        <$  reservedWord "define"
        <*> identifier
        <*> optional (reservedWord ":" *> expr)
        <*  reservedWord ":="
        <*> expr

assume :: Parser (Statement P)
assume =
    Assume <$ reservedWord "assume" <*> identifier <* reservedWord ":" <*> expr

prove :: Parser (Statement P)
prove =
    Prove <$ reservedWord "prove" <*> identifier <* reservedWord ":" <*> expr

statement :: Parser (Statement P)
statement = define <|> assume <|> prove

statements :: Parser [Statement P]
statements = sc *> many statement <* eof
