{-# LANGUAGE OverloadedStrings #-}
-- Source locations.
module Location
    ( Range(..)
    , spanRange
    , Ident(..)
    ) where

import           Data.Aeson
import           Data.Text                      ( Text )

-- A half-open interval of text in the source file, represented by two offsets
-- of Unicode code points.
data Range = Range !Int !Int
    deriving (Eq)

instance Show Range where
    show (Range s e) = show s ++ ":" ++ show e

instance ToJSON Range where
    toJSON (Range s e) = object ["start" .= s, "end" .= e]

-- Returns a range that covers both given range. The first range must be before
-- the second.
spanRange :: Range -> Range -> Range
spanRange (Range s _) (Range _ e) = Range s e

-- A range, along with the text that occupies that range.
data Ident = Ident
    { identRange :: !Range
    , identText :: !Text
    }
    deriving (Eq, Show)
