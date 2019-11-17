{-# LANGUAGE OverloadedStrings #-}
module Parser
    ( statements
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
    e <- getOffset
    return (Range s e)

identifier :: Parser Ident
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
    e <- getOffset
    return (Range s e)

params :: Parser [Param Range Ident]
params = symbol '(' *> param `sepBy1` symbol ',' <* symbol ')'
    where param = (,) <$> identifier <* reservedWord ":" <*> expr

atom :: Parser (Expr Range Ident)
atom = hole <|> var <|> type_ <|> sigma <|> pi_ <|> lam <|> tuple
  where
    hole = Hole <$> reservedWord "_"
    var  = do
        i <- identifier
        return (Var (location i) i)
    type_ = Type <$> reservedWord "Type"
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
        return (Lam (spanRange s (ann e)) p e)
    tuple = do
        s  <- symbol '('
        es <- expr `sepBy1` symbol ','
        e  <- symbol ')'
        return (Tuple (spanRange s e) es)

apps :: Parser (Expr Range Ident)
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

expr :: Parser (Expr Range Ident)
expr = makeExprParser
    apps
    [ [InfixR (binop Times <$ reservedWord "×")]
    , [InfixN (binop Equal <$ reservedWord "=")]
    , [InfixR (binop Arrow <$ reservedWord "→")]
    ]
    where binop c e1 e2 = c (spanRange (ann e1) (ann e2)) e1 e2

define :: Parser (Statement Range Ident)
define =
    Define
        <$  reservedWord "define"
        <*> identifier
        <*> (params <|> return [])
        <*> optional (reservedWord ":" *> expr)
        <*  reservedWord ":="
        <*> expr

assume :: Parser (Statement Range Ident)
assume =
    Assume <$ reservedWord "assume" <*> identifier <* reservedWord ":" <*> expr

prove :: Parser (Statement Range Ident)
prove =
    Prove <$ reservedWord "prove" <*> identifier <* reservedWord ":" <*> expr

statement :: Parser (Statement Range Ident)
statement = define <|> assume <|> prove

statements :: Parser [Statement Range Ident]
statements = sc *> many statement <* eof
