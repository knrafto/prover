{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad
import           Data.Monoid
import           System.Exit
import           System.IO

import           Data.Aeson
import qualified Data.ByteString.Lazy.Char8    as B
import           Data.Maybe
import qualified Data.Text.IO                  as Text
import           Text.Megaparsec               hiding (Token, tokens)
import           Text.Pretty.Simple

import Prover.Monad
import Prover.ScopeCheck
import Prover.Parser

import           Diagnostic
import qualified Flags
import           Location
import           Monad
import           ScopeCheck
import           Syntax
import           TypeCheck
import           Parser

data HighlightedRange = HighlightedRange Range String
    deriving (Show)

instance ToJSON HighlightedRange where
    toJSON (HighlightedRange r s) = object ["range" .= r, "kind" .= s]

data Response = Response
    { highlighting :: [HighlightedRange]
    , diagnostics  :: [Diagnostic]
    }
    deriving (Show)

instance ToJSON Response where
    toJSON r = object ["highlighting" .= highlighting r, "diagnostics" .= diagnostics r]

nameHighlighting :: [Name] -> [HighlightedRange]
nameHighlighting = map (\n -> HighlightedRange (identRange (nameUsage n)) (nameClass n))
  where
    nameClass n = case nameKind n of
        Local   -> "local_name"
        Defined -> "defined_name"
        Assumed -> "assumed_name"
        Unbound -> "unbound_name"

extractNames :: [Statement N] -> [Name]
extractNames stmts = appEndo (foldMap (foldNames (\n -> Endo (n :))) stmts) []

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
        abstract <- runTCM $ scopeCheckModule concrete
        print abstract
        -- stmts <- case parse statements path input of
        --     Left  e -> die (errorBundlePretty e)
        --     Right x -> return x
        -- when Flags.print_parse $ pPrint stmts
        -- let stmts' = scopeCheck stmts
        -- result <- runTcM $ do
        --     stmts'' <- typeCheck stmts'
        --     unless Flags.json $ printStatements stmts''
        -- ds <- case result of
        --     Left  d -> do
        --         unless Flags.json $ do
        --             putStrLn $ "Error at " ++ show (diagnosticRange d)
        --             putStrLn (diagnosticMessage d)
        --         return [d]
        --     Right _ -> return []
        -- let r = Response
        --         { highlighting = nameHighlighting (extractNames stmts')
        --         , diagnostics  = ds
        --         }
        -- when Flags.json $ B.putStrLn (encode r)
