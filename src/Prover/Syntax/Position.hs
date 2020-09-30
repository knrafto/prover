-- | Source locations and ranges.
module Prover.Syntax.Position where

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
    -- | 0-indexed file offset, in Unicode characters.
  , positionOffset  :: !Int
  } deriving (Eq, Show)

instance Pretty Position where
  pretty p = pretty (positionLine p) <> ":" <> pretty (positionColumn p)

instance ToJSON Position where
  toJSON p = toJSON (positionOffset p)

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

class HasRange a where
  getRange :: a -> Range

-- TODO: does this really belong here? Maybe rename "Prover.Syntax.Position" to
-- "Prover.Syntax.Common" or something
data Fixity = Infix | Infixl | Infixr
  deriving (Eq, Show)
