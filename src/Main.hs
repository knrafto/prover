module Main where

import           System.Environment
import           System.Exit
import           System.IO

import qualified Data.Text.IO                  as Text
import           Text.Megaparsec

import TypeCheck
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
        _ -> panic "usage: prover FILE"
    withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        stmts <- case parse statements path input of
            Left e -> panic (errorBundlePretty e)
            Right x -> return x
        _ <- typeCheck stmts
        return ()