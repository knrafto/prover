module Main where

import           System.Environment
import           System.IO

import           Data.Text                      ( Text )
import qualified Data.Text.IO                  as Text
import           Text.Megaparsec
import           Text.Pretty.Simple

import Syntax
import Parser

compile :: Text -> IO ()
compile input = case parse defns "" input of
    Left e -> putStr (errorBundlePretty e)
    Right x -> pPrint x

main :: IO ()
main = getArgs >>= \args -> case args of
    [path] -> withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        compile input
    [] -> hPutStrLn stderr "usage: prover FILE"
