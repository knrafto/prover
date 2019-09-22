{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad
import System.Environment
import System.IO

import Data.Text (Text)
import qualified Data.Text.IO as Text
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- Lots of parsing stuff from https://markkarpov.com/megaparsec/megaparsec.html
type Parser = Parsec Void Text

lineComment :: Parser ()
lineComment = L.skipLineComment "#"

scn :: Parser ()
scn = L.space space1 lineComment empty

sc :: Parser ()
sc = L.space (void $ some (char ' ' <|> char '\t')) lineComment empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme (scn <* eof)

compile :: Text -> IO ()
compile = parseTest (scn <* eof)

main :: IO ()
main = getArgs >>= \args -> case args of
    [path] -> withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        compile input
    [] -> hPutStrLn stderr "usage: prover FILE"
