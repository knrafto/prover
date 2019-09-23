module Main where

import           System.Environment
import           System.Exit
import           System.IO

import           Data.Text                      ( Text )
import qualified Data.Text.IO                  as Text
import           Text.Megaparsec
import           Text.Pretty.Simple

import Syntax
import Parser

panic :: String -> IO a
panic message = do
    hPutStrLn stderr message
    exitWith (ExitFailure 1)

main :: IO ()
main = do
    args <- getArgs
    path <- case args of
        [path] -> return path
        [] -> panic "usage: prover FILE"
    withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        case parse statements path input of
            Left e -> putStr (errorBundlePretty e)
            Right x -> pPrint x