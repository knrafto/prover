{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
module Prover.Parser ( parseModule ) where

import Control.Monad

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
isWordChar c = c `notElem` (" \t\r\n\f\v(){},." :: [Char])

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
name = lexeme. try $ do
    s <- getPosition
    w <- takeWhile1P (Just "word character") isWordChar
    e <- getPosition
    when (w `elem` reservedWords) $ fail
        (  "keyword "
        ++ T.unpack w
        ++ " is reserved and cannot be used as a name"
        )
    return (Name (Range s e) w)
  where
    reservedWords :: [Text]
    reservedWords =
        [ "_"
        , ":"
        , "≡"
        , "Σ"
        , "Π"
        , "λ"
        , "Type"
        , "define"
        , "axiom"
        , "rewrite"
        , "where"
        , "infix"
        , "infixl"
        , "infixr"
        ]

text :: Parser Text
text = do
    Name _ s <- name
    return s

number :: Parser Int
number = do
    s <- text
    case reads (T.unpack s) of
        [(i, "")] -> return i
        _         -> fail $ T.unpack s ++ " is not a number"

symbol :: Char -> Parser Range
symbol c = lexeme $ do
    s <- getPosition
    _ <- char c
    Range s <$> getPosition

-- TODO: this also parses {x y z}, which is incorrect
implicitParams :: Parser [ParamGroup]
implicitParams = many $ ParamGroup <$ symbol '{' <*> some name <*> optional (reservedWord ":" *> expr) <* symbol '}'

explicitParams :: Parser [ParamGroup]
explicitParams = many (annotated <|> bare)
  where
    annotated = ParamGroup <$ symbol '(' <*> some name <* reservedWord ":" <*> (Just <$> expr) <* symbol ')'
    bare      = (\n -> ParamGroup [n] Nothing) <$> name

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
        p <- explicitParams
        _ <- symbol '.'
        e <- expr
        return (Pi (rangeSpan s (getRange e)) p e)
    lam = do
        s <- reservedWord "λ"
        p <- explicitParams
        _ <- symbol '.'
        e <- expr
        return (Lam (rangeSpan s (getRange e)) p e)
    sigma = do
        s <- reservedWord "Σ"
        p <- explicitParams
        _ <- symbol '.'
        e <- expr
        return (Sigma (rangeSpan s (getRange e)) p e)

expr :: Parser Expr
expr = do
    es <- some atom
    case es of
        [e] -> return e
        _   -> do
            let r = foldr1 rangeSpan (map getRange es)
            return (Apps r es)

define :: Parser Decl
define = Define
    <$  reservedWord "define"
    <*> name
    <*> implicitParams
    <*> explicitParams
    <*> optional (reservedWord ":" *> expr)
    <*  reservedWord "≡"
    <*> expr

axiom :: Parser Decl
axiom = Assume
    <$  reservedWord "axiom"
    <*> name
    <*> implicitParams
    <*> explicitParams
    <*  reservedWord ":"
    <*> expr

rewrite :: Parser Decl
rewrite = Rewrite
    <$  reservedWord "rewrite"
    <*> name
    <*> explicitParams
    <*  reservedWord "where"
    <*> expr
    <*  reservedWord "≡"
    <*> expr

fixity :: Parser Decl
fixity = Fixity
    <$> (Infix  <$ reservedWord "infix"  <|>
         Infixl <$ reservedWord "infixl" <|>
         Infixr <$ reservedWord "infixr")
    <*> number
    <*> text

decl :: Parser Decl
decl = define <|> axiom <|> rewrite <|> fixity

module_ :: Parser Module
module_ = Module <$ sc <*> many decl <* eof

parseModule :: FilePath -> Text -> Either String Module
parseModule path input = case parse module_ path input of
    Left  e -> Left (errorBundlePretty e)
    Right m -> Right m
