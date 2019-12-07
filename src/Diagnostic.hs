{-# LANGUAGE OverloadedStrings #-}
module Diagnostic where

import Data.Aeson
import Data.Text (Text)

import Location

data Diagnostic = Diagnostic !Range !Text
    deriving (Show)

instance ToJSON Diagnostic where
    toJSON (Diagnostic r m) = object ["range" .= r, "message" .= m]
