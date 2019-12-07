{-# LANGUAGE OverloadedStrings #-}
module Diagnostic where

import Data.Aeson

import Location

data Diagnostic = Diagnostic
    { diagnosticRange :: !Range
    , diagnosticMessage :: String
    }
    deriving (Show)

instance ToJSON Diagnostic where
    toJSON (Diagnostic r m) = object ["range" .= r, "message" .= m]
