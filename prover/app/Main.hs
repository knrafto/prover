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
    let ls = splitLines input
    let groups = groupIndentedLines ls
    forM_ groups $ \group -> do
        putStrLn "---"
        forM_ group $ \line -> putStrLn (show line)
        forM_ groups $ \group -> do
            putStrLn "---"
            forM_ group $ \line ->
                forM_ (tokenizeLine line) $ \token ->
                    putStrLn (show token)

main :: IO ()
main = getArgs >>= \args -> case args of
    [path] -> withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        processInput input
    [] -> hPutStrLn stderr "usage: prover FILE"
