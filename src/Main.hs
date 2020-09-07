{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           System.Exit
import           System.IO

import           Data.Aeson
import qualified Data.ByteString.Lazy.Char8    as B
import qualified Data.Text.IO                  as Text
import           Text.Megaparsec               hiding (Token, tokens)

import Prover.Interaction
import Prover.Monad
import Prover.Parser

import qualified Flags

main :: IO ()
main = do
  path <- case Flags.positionalArgs of
    [path] -> return path
    _      -> die "usage: prover FILE"
  withFile path ReadMode $ \handle -> do
    input <- Text.hGetContents handle
    concrete <- case parse module_ path input of
      Left  e -> die (errorBundlePretty e)
      Right x -> return x
    result <- runM _
    let r = case result of
          Left err -> Response
            { highlighting = []
            , diagnostics  = [diagnoseErr err]
            }
          Right m  -> Response
            { highlighting = highlightModule m
            , diagnostics  = []
            }
    B.putStrLn (encode r)
