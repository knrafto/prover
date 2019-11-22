{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad
import           System.Exit
import           System.IO

import           Data.Aeson
import qualified Data.ByteString.Lazy.Char8    as B
import qualified Data.Text.IO                  as Text
import           Text.Megaparsec    hiding (Token, tokens)
import           Text.Pretty.Simple

import qualified Flags
import           Naming
import           TypeCheck
import           Parser
import           Token

panic :: String -> IO a
panic message = do
    hPutStrLn stderr message
    exitWith (ExitFailure 1)

data Response = Response
    { tokens :: [Token]
    , names :: [Name]
    }
    deriving (Show)

instance ToJSON Response where
    toJSON r = object ["tokens" .= tokens r, "names" .= names r]

main :: IO ()
main = do
    path <- case Flags.positionalArgs of
        [path] -> return path
        _      -> panic "usage: prover FILE"
    withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        let ts = tokenize input
        when Flags.print_tokens $ forM_ ts print
        stmts <- case parse statements path input of
            Left  e -> panic (errorBundlePretty e)
            Right x -> return x
        when Flags.print_parse $ pPrint stmts
        let stmts' = resolveNames stmts
        let r      = Response { tokens = ts, names = extractNames stmts' }
        when Flags.json $ B.putStrLn (encode r)
        unless Flags.json $ do
            result <- runTcM (typeCheck stmts')
            case result of
                Nothing           -> putStrLn "Terminated with error"
                Just (stmts'', _) -> printStatements stmts''
