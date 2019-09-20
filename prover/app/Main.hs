module Main where

import Control.Monad
import System.Environment
import System.IO

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text

import Lib

processInput :: Text -> IO ()
processInput input = do
    forM_ (splitLines input) $ \line -> putStrLn (show line)

main :: IO ()
main = getArgs >>= \args -> case args of
    [path] -> withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        processInput input
    [] -> hPutStrLn stderr "usage: prover FILE"
