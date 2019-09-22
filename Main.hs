{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad
import           System.Environment
import           System.IO

import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import qualified Data.Text.IO                  as Text
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

-- AST
type Module = [Defn]

data Defn = Defn
    { defnName :: Text
    , defnParams :: Params
    , defnType :: Expr
    , defnBody :: Expr
    } deriving (Show)

type Params = [(Text, Expr)]

data Expr
    = Var Text
    | Call Expr [Expr]
    | Sigma Params Expr
    | Pi Params Expr
    | Lambda Params Expr
    | Arrow Expr Expr
    | Eq Expr Expr
    deriving (Show)

-- Lots of parsing stuff from https://markkarpov.com/megaparsec/megaparsec.html
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
    reservedWords = [":", ":=", "=", "Σ", "Π", "λ", "→"]

symbol :: Char -> Parser ()
symbol c = lexeme (void $ char c)

expr :: Parser Expr
expr = Var <$> identifier  -- TODO

params :: Parser Params
params = between (symbol '(') (symbol ')') $ param `sepBy1` symbol ','
    where param = (,) <$> identifier <* reservedWord ":" <*> expr

defn :: Parser Defn
defn = L.nonIndented sc $ do
    name <- identifier
    ps   <- params
    reservedWord ":"
    t <- expr
    reservedWord ":="
    b <- expr
    return $ Defn { defnName   = name
                  , defnParams = ps
                  , defnType   = t
                  , defnBody   = b
                  }

compile :: Text -> IO ()
compile = parseTest (many defn <* eof)

main :: IO ()
main = getArgs >>= \args -> case args of
    [path] -> withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        compile input
    [] -> hPutStrLn stderr "usage: prover FILE"
