module Main where

import           Control.Monad
import           System.Environment
import           System.Exit
import           System.IO

import qualified Data.Map.Strict               as Map
import qualified Data.Text                     as Text
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
        env <- typeCheck stmts
        forM_ (Map.toList (envAssumptions env)) $ \(name, _A) ->
            putStrLn $ ":assume " ++ Text.unpack name ++ " : " ++ show _A
        forM_ (Map.toList (envDefinitions env)) $ \(name, body) ->
            putStrLn $ Text.unpack name ++ " := " ++ show body