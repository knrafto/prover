{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad
import System.Exit
import System.IO

import Data.Aeson
import Data.ByteString.Lazy.Char8 qualified as B
import Data.Text.IO qualified as Text

import Prover.InfixParser qualified as InfixParser
import Prover.Interaction
import Prover.Flags qualified as Flags
import Prover.Monad
import Prover.Parser
import Prover.TypeCheck qualified as TypeCheck

main :: IO ()
main = do
  path <- case Flags.positionalArgs of
    [path] -> return path
    _      -> die "usage: prover FILE"
  withFile path ReadMode $ \handle -> do
    input <- Text.hGetContents handle
    m <- case parseModule path input of
      Left  s -> die s
      Right x -> return x
    (m, state) <- runM $ do
      m' <- InfixParser.processModule m
      TypeCheck.checkModule m'
    let r = Response
          { highlighting = highlightModule m
          , diagnostics  = map diagnoseError (errors state)
          }
    when Flags.json $ B.putStrLn (encode r)
