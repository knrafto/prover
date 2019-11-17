{-# LANGUAGE OverloadedStrings #-}
module Parser
    ( statements
    )
where

import           Control.Monad

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

symbol :: Char -> Parser ()
symbol c = lexeme (void $ char c)

located :: Parser a -> Parser (Located a)
located m = do
    s <- getOffset
    a <- m
    e <- getOffset
    return (L (Range s e) a)

params :: Parser [Param]
params = symbol '(' *> param `sepBy1` symbol ',' <* symbol ')'
    where param = (,) <$> identifier <* reservedWord ":" <*> expr

atom :: Parser LExpr
atom = located $ choice
    [ Hole <$ reservedWord "_"
    , Ident <$> identifier
    , Type <$ reservedWord "Type"
    , SigmaExpr <$ reservedWord "Σ" <*> params <*> expr
    , PiExpr <$ reservedWord "Π" <*> params <*> expr
    , LamExpr <$ reservedWord "λ" <*> params <*> expr
    , Tuple <$ symbol '(' <*> expr `sepBy1` symbol ',' <* symbol ')'
    ]

apps :: Parser LExpr
apps = do
    s <- getOffset
    x <- atom
    rest s x
  where
    rest s x = app s x <|> return x

    app s x = do
        symbol '('
        args <- expr `sepBy1` symbol ','
        symbol ')'
        e <- getOffset
        rest s (L (Range s e) (AppExpr x args))

pInfixN :: Parser (LExpr -> LExpr -> Expr) -> Parser LExpr -> Parser LExpr
pInfixN op p = do
    s <- getOffset
    x <- p
    rest s x <|> return x
  where
    rest s x = do
        f <- op
        y <- p
        e <- getOffset
        return (L (Range s e) (f x y))

pInfixR :: Parser (LExpr -> LExpr -> Expr) -> Parser LExpr -> Parser LExpr
pInfixR op p = do
    s <- getOffset
    x <- p
    rest s x
  where
    rest s x = rest' s x <|> return x

    rest' s x = do
        f <- op
        y <- pInfixR op p
        e <- getOffset
        rest s (L (Range s e) (f x y))

expr :: Parser LExpr
expr = expr'
  where
    times  = pInfixR (Times <$ reservedWord "×") apps
    equals = pInfixN (Equal <$ reservedWord "=") times
    expr'  = pInfixR (Arrow <$ reservedWord "→") equals

define :: Parser Statement
define =
    Define
        <$  reservedWord "define"
        <*> identifier
        <*> (params <|> return [])
        <*> optional (reservedWord ":" *> expr)
        <*  reservedWord ":="
        <*> expr

assume :: Parser Statement
assume =
    Assume <$ reservedWord "assume" <*> identifier <* reservedWord ":" <*> expr

prove :: Parser Statement
prove =
    Prove <$ reservedWord "prove" <*> identifier <* reservedWord ":" <*> expr

statement :: Parser LStatement
statement = located $ define <|> assume <|> prove

statements :: Parser [LStatement]
statements = sc *> many statement <* eof
