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

import           Diagnostic
import qualified Flags
import           Location
import           Monad
import           Naming
import           Syntax
import           Token (Token(..))
import qualified Token
import           TypeCheck
import           Parser

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
    , diagnostics  :: [Diagnostic]
    }
    deriving (Show)

instance ToJSON Response where
    toJSON r = object ["highlighting" .= highlighting r, "diagnostics" .= diagnostics r]

tokenHighlighting :: [Token] -> [HighlightedRange]
tokenHighlighting = mapMaybe $ \t -> case tokenClass t of
    Nothing -> Nothing
    Just s -> Just (HighlightedRange (identRange (tokenIdent t)) s)
  where
    tokenClass t = case tokenKind t of
        Token.Identifier  -> Nothing
        Token.LParen      -> Just "lparen"
        Token.RParen      -> Just "rparen"
        Token.Comma       -> Just "comma"
        Token.Dot         -> Just "dot"
        Token.Underscore  -> Just "underscore"
        Token.Colon       -> Just "colon"
        Token.DefEquals   -> Just "def_equals"
        Token.Sigma       -> Just "sigma"
        Token.Pi          -> Just "pi"
        Token.Lambda      -> Just "lambda"
        Token.Equals      -> Just "equals"
        Token.Times       -> Just "times"
        Token.Arrow       -> Just "arrow"
        Token.Type        -> Just "type"
        Token.Define      -> Just "define"
        Token.Assume      -> Just "assume"
        Token.Prove       -> Just "prove"


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
        _      -> panic "usage: prover FILE"
    withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        let tokens = Token.tokenize input
        when Flags.print_tokens $ forM_ tokens print
        stmts <- case parse statements path input of
            Left  e -> panic (errorBundlePretty e)
            Right x -> return x
        when Flags.print_parse $ pPrint stmts
        let stmts' = resolveNames stmts
        result <- runTcM (typeCheck stmts')
        ds <- case result of
            Left  d            -> do
                unless Flags.json $ do
                    putStrLn $ "Error at " ++ show (diagnosticRange d)
                    putStrLn (diagnosticMessage d)
                return [d]
            Right (stmts'', _) -> do
                unless Flags.json $ printStatements stmts''
                return []
        let r = Response
                { highlighting = tokenHighlighting tokens ++ nameHighlighting (extractNames stmts')
                , diagnostics  = ds
                }
        when Flags.json $ B.putStrLn (encode r)
