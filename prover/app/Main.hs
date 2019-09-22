module Main where

import Control.Monad
import System.Environment
import System.IO

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text

import Lib

compile :: Text -> IO ()
compile input = do
    let tokens = tokenize input
    forM_ tokens $ \token -> putStrLn (show token)

main :: IO ()
main = getArgs >>= \args -> case args of
    [path] -> withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        compile input
    [] -> hPutStrLn stderr "usage: prover FILE"
