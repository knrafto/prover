-- | Source locations and ranges.
module Prover.Syntax.Position where

-- | A half-open interval of text in the source file, represented by two
-- 0-indexed Unicode character offsets.
data Range = Range
  { rangeStart :: !Int
  , rangeEnd   :: !Int
  } deriving (Eq, Show)

-- | Construct a range that covers both given range. The first range must be
-- before the second.
rangeSpan :: Range -> Range -> Range
rangeSpan (Range s _) (Range _ e) = Range s e

class HasRange a where
  getRange :: a -> Range
