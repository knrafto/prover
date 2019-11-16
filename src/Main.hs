module Main where

import           Control.Monad
import           System.Exit
import           System.IO

import qualified Data.Text.IO                  as Text
import           Text.Megaparsec
import           Text.Pretty.Simple

import qualified Flags
import Location
import TypeCheck
import Parser
import Token

panic :: String -> IO a
panic message = do
    hPutStrLn stderr message
    exitWith (ExitFailure 1)

main :: IO ()
main = do
    path <- case Flags.positionalArgs of
        [path] -> return path
        _ -> panic "usage: prover FILE"
    withFile path ReadMode $ \handle -> do
        input <- Text.hGetContents handle
        when Flags.print_tokens $
            forM_ (tokenize input) $ \(L l t) ->
                putStrLn (show l ++ ": " ++ show t)
        stmts <- case parse statements path input of
            Left e -> panic (errorBundlePretty e)
            Right x -> return x
        when Flags.print_parse $ pPrint stmts
        void $ typeCheck stmts
