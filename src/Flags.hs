module Flags where

import Data.List

import System.Environment
import System.IO.Unsafe

commandLine :: [String]
commandLine = unsafePerformIO getArgs

{-# NOINLINE commandLine #-}

-- Split command line into lists of flag names and positional args.
splitArgs :: [String] -> ([String], [String])
splitArgs args = case args of
    [] -> ([], [])
    arg:rest
        | arg == "--" -> ([], rest)
        | "--" `isPrefixOf` arg -> let (flags, posArgs) = splitArgs rest in (arg : flags, posArgs)
        | otherwise -> let (flags, posArgs) = splitArgs rest in (flags, arg : posArgs)

commandLineFlags :: [String]
commandLineFlags = fst (splitArgs commandLine)

positionalArgs :: [String]
positionalArgs = snd (splitArgs commandLine)
    
boolFlag :: String -> Bool
boolFlag name = "--" ++ name `elem` commandLineFlags

print_tokens :: Bool
print_tokens = boolFlag "print_tokens"

print_parse :: Bool
print_parse = boolFlag "print_parse"

print_trace :: Bool
print_trace = boolFlag "print_trace"