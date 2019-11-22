{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad
import           System.Exit
import           System.IO

import           Data.Aeson
import qualified Data.ByteString.Lazy.Char8    as B
import           Data.Maybe
import qualified Data.Text.IO                  as Text
import           Text.Megaparsec    hiding (Token, tokens)
import           Text.Pretty.Simple

import qualified Flags
import           Location
import           Naming
import           TypeCheck
import           Parser
import           Token

panic :: String -> IO a
panic message = do
    hPutStrLn stderr message
    exitWith (ExitFailure 1)

data HighlightedRange = HighlightedRange Range String
    deriving (Show)

instance ToJSON HighlightedRange where
    toJSON (HighlightedRange r s) = object ["range" .= r, "kind" .= s]

data Response = Response
    { highlighting :: [HighlightedRange]
    }
    deriving (Show)

instance ToJSON Response where
    toJSON r = object ["highlighting" .= highlighting r]

tokenHighlighting :: [Token] -> [HighlightedRange]
tokenHighlighting = mapMaybe $ \case
    Identifier _ -> Nothing
    ReservedWord i -> Just (HighlightedRange (location i) "reserved_word")
    Symbol i -> Just (HighlightedRange (location i) "symbol")

nameHighlighting :: [Name] -> [HighlightedRange]
nameHighlighting = map $ \case
    Local i _ -> HighlightedRange (location i) "local"
    Defined i _ -> HighlightedRange (location i) "global"
    Assumed i _ -> HighlightedRange (location i) "global"
    Unbound i -> HighlightedRange (location i) "local"

main :: IO ()
main = do
    path <- case Flags.positionalArgs of
        [path] -> return path
        _      -> panic "usage: prover FILE"
    withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        let tokens = tokenize input
        when Flags.print_tokens $ forM_ tokens print
        stmts <- case parse statements path input of
            Left  e -> panic (errorBundlePretty e)
            Right x -> return x
        when Flags.print_parse $ pPrint stmts
        let stmts' = resolveNames stmts
        let r      = Response { highlighting = tokenHighlighting tokens ++ nameHighlighting (extractNames stmts') }
        when Flags.json $ B.putStrLn (encode r)
        unless Flags.json $ do
            result <- runTcM (typeCheck stmts')
            case result of
                Nothing           -> putStrLn "Terminated with error"
                Just (stmts'', _) -> printStatements stmts''
