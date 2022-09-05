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

import Prover.Position
import Prover.Syntax

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

isWordChar :: Char -> Bool
isWordChar c = c `notElem` (" \t\r\n(){},." :: [Char])

getPosition :: Parser Position
getPosition = do
    SourcePos _ l c <- getSourcePos
    Position (unPos l) (unPos c) <$> getOffset

reservedWord :: Text -> Parser Range
reservedWord w = lexeme . try $ do
    s <- getPosition
    _ <- string w
    notFollowedBy (satisfy isWordChar)
    Range s <$> getPosition

ident :: Parser Ident
ident = lexeme . try $ do
    s <- getPosition
    w <- takeWhile1P (Just "word character") isWordChar
    when (w `elem` reservedWords) $ fail
        (  "keyword "
        ++ T.unpack w
        ++ " is reserved and cannot be used as an identifier"
        )
    e <- getPosition
    return (Ident (Range s e) w)
  where
    reservedWords :: [Text]
    reservedWords =
        [ "_"
        , "?"
        , "!"
        , ":"
        , "≡"
        , "Σ"
        , "Π"
        , "λ"
        , "→"
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
    Ident _ s <- ident
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
implicitParams :: Parser [ParamGroup Range Ident]
implicitParams = many $ ParamGroup <$ symbol '{' <*> some ident <*> optional (reservedWord ":" *> expr) <* symbol '}'

explicitParams :: Parser [ParamGroup Range Ident]
explicitParams = many (annotated <|> bare)
  where
    annotated = ParamGroup <$ symbol '(' <*> some ident <* reservedWord ":" <*> (Just <$> expr) <* symbol ')'
    bare      = (\n -> ParamGroup [n] Nothing) <$> ident

atom :: Parser (Expr Range Ident)
atom = var <|> hole <|> goal <|> type_ <|> parens <|> sigma <|> pi_ <|> lam
  where
    var   = do
        id <- ident
        return $ EVar (identRange id) id
    hole  = EHole <$> reservedWord "_"
    goal  = EGoal <$> reservedWord "?" <*> pure UserGoal
        <|> EGoal <$> reservedWord "!" <*> pure ProofSearchGoal
    type_ = EType <$> reservedWord "Type"
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
        return (EPi (rangeSpan s (ann e)) p e)
    lam = do
        s <- reservedWord "λ"
        p <- explicitParams
        _ <- symbol '.'
        e <- expr
        return (ELam (rangeSpan s (ann e)) p e)
    sigma = do
        s <- reservedWord "Σ"
        p <- explicitParams
        _ <- symbol '.'
        e <- expr
        return (ESigma (rangeSpan s (ann e)) p e)

apps :: Parser (Expr Range Ident)
apps = do
    es <- some atom
    case es of
        [e] -> return e
        _   -> do
            let r = foldr1 rangeSpan (map ann es)
            return (EApps r es)

expr :: Parser (Expr Range Ident)
expr = makeExprParser
    apps
    [ [InfixR (binop EArrow  <$ reservedWord "→")]
    , [InfixR (binop EPair   <$ symbol       ',')]
    ]
    where binop c e1 e2 = c (rangeSpan (ann e1) (ann e2)) e1 e2

define :: Parser (Decl Range Ident)
define = Define
    <$  reservedWord "define"
    <*> ident
    <*> implicitParams
    <*> explicitParams
    <*> optional (reservedWord ":" *> expr)
    <*  reservedWord "≡"
    <*> expr

axiom :: Parser (Decl Range Ident)
axiom = Assume
    <$  reservedWord "axiom"
    <*> ident
    <*> implicitParams
    <*> explicitParams
    <*  reservedWord ":"
    <*> expr

rewrite :: Parser (Decl Range Ident)
rewrite = Rewrite
    <$  reservedWord "rewrite"
    <*> ident
    <*> explicitParams
    <*  reservedWord "where"
    <*> expr
    <*  reservedWord "≡"
    <*> expr

fixity :: Parser (Decl Range Ident)
fixity = Fixity
    <$> (Infix  <$ reservedWord "infix"  <|>
         Infixl <$ reservedWord "infixl" <|>
         Infixr <$ reservedWord "infixr")
    <*> number
    <*> text

decl :: Parser (Decl Range Ident)
decl = define <|> axiom <|> rewrite <|> fixity

module_ :: Parser (Module Range Ident)
module_ = Module <$ sc <*> many decl <* eof

parseModule :: FilePath -> Text -> Either String (Module Range Ident)
parseModule path input = case parse module_ path input of
    Left  e -> Left (errorBundlePretty e)
    Right m -> Right m
