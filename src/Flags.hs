module Flags where

import Data.List

import System.Environment
import System.IO.Unsafe

-- Split command line into lists of flag names and positional args.
splitArgs :: [String] -> ([String], [String])
splitArgs args = case args of
    [] -> ([], [])
    arg:rest
        | arg == "--" -> ([], rest)
        | "--" `isPrefixOf` arg -> let (flags, posArgs) = splitArgs rest in (arg : flags, posArgs)
        | otherwise -> let (flags, posArgs) = splitArgs rest in (flags, arg : posArgs)

positionalArgs :: [String]
positionalArgs = unsafePerformIO $ do
    (_, posArgs) <- splitArgs <$> getArgs
    return posArgs
    
getFlag :: String -> Bool
getFlag name = unsafePerformIO $ do
    (flags, _) <- splitArgs <$> getArgs
    return ("--" ++ name `elem` flags)

print_tokens :: Bool
print_tokens = getFlag "print_tokens"

print_parse :: Bool
print_parse = getFlag "print_parse"

print_trace :: Bool
print_trace = getFlag "print_trace"