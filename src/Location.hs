{-# LANGUAGE OverloadedStrings #-}
module Location where

import           Data.Aeson
import           Data.Text                      ( Text )

-- A range of text in the source file, represented by two offsets in Unicode
-- code points.
data Range = Range !Int !Int
    deriving (Eq)

instance Show Range where
    show (Range s e) = show s ++ ":" ++ show e

instance ToJSON Range where
    toJSON (Range s e) = object ["start" .= s, "end" .= e]

spanRange :: Range -> Range -> Range
spanRange (Range s _) (Range _ e) = Range s e

data Located e = L Range e

instance Show e => Show (Located e) where
    showsPrec d (L _ e) = showsPrec d e

location :: Located e -> Range
location (L l _) = l

unLoc :: Located e -> e
unLoc (L _ e) = e

type Ident = Located Text

-- A range and enum representing style information.
data Decoration = Decoration Range String
    deriving (Show)

instance ToJSON Decoration where
    toJSON (Decoration range scope) =
        object ["range" .= range, "kind" .= scope]

-- Interaction response
data Response = Response { decorations :: [Decoration] }
    deriving (Show)

instance ToJSON Response where
    toJSON r = object ["decorations" .= decorations r]
