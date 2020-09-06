-- Source locations and ranges.
module Prover.Syntax.Position where

-- A source position, as 1-indexed line and column numbers.
data Position = Position !Int !Int
  deriving (Eq, Show)

-- A half-open interval of text in the source file, represented by two
-- positions.
data Range = Range
  { rangeStart :: !Position
  , rangeEnd   :: !Position
  } deriving (Eq, Show)

-- Get the range of a BNFC parser token.
tokenRange :: ((Int, Int), String) -> Range
tokenRange ((l, c), s) = Range (Position l c) (Position l (c + length s))

-- Returns a range that covers both given range. The first range must be before
-- the second.
rangeSpan :: Range -> Range -> Range
rangeSpan (Range s _) (Range _ e) = Range s e
