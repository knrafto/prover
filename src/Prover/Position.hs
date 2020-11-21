-- | Source locations and ranges.
module Prover.Position where

import Data.Char

import Data.Aeson
import Prettyprinter

-- | A position in the source file. A position is like a cursor position, not a
-- character position: it represents the space "between" two characters (or at
-- the beginning or end of the file).
data Position = Position
  { -- | 1-indexed line number.
    positionLine    :: !Int
    -- | 1-indexed column number. Each Unicode character counts as one column,
    -- except for tab (which takes 8 columns) and newline (which starts a new
    -- line).
  , positionColumn  :: !Int
    -- | 0-indexed file offset, in UTF-16(!) code units for VS Code.
  , positionUtf16Offset  :: !Int
  } deriving (Eq, Show)

instance Pretty Position where
  pretty p = pretty (positionLine p) <> ":" <> pretty (positionColumn p)

instance ToJSON Position where
  toJSON p = toJSON (positionUtf16Offset p)

startPosition :: Position
startPosition = Position 1 1 0

utf16Length :: Char -> Int
utf16Length c = if ord c <= 0xFFFF then 1 else 2

advancePosition :: Char -> Position -> Position
advancePosition '\t' (Position l c o) = Position l (c + 8) (o + 1)
advancePosition '\n' (Position l _ o) = Position (l + 1) 1 (o + 1)
advancePosition a    (Position l c o) = Position l (c + 1) (o + utf16Length a)

-- | An interval of text in the source file, represented by two positions.
data Range = Range
  { rangeStart :: !Position
  , rangeEnd   :: !Position
  } deriving (Eq, Show)

instance Pretty Range where
  pretty (Range s e) = pretty s <> "-" <> pretty e

instance ToJSON Range where
  toJSON (Range s e) = object ["start" .= s, "end" .= e]

-- | Construct a range that covers both given range. The first range must be
-- before the second.
rangeSpan :: Range -> Range -> Range
rangeSpan (Range s _) (Range _ e) = Range s e

-- TODO: delete?
class HasRange a where
  getRange :: a -> Range

-- TODO: move to "Prover.Syntax"
data Fixity = Infix | Infixl | Infixr
  deriving (Eq, Show)
