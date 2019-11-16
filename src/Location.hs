module Location where

-- A range of text in the source file, represented by two offsets.
data SrcSpan = SrcSpan !Int !Int
    deriving (Eq)

instance Show SrcSpan where
    show (SrcSpan s e) = show s ++ ":" ++ show e

data Located e = L SrcSpan e

instance Show e => Show (Located e) where
    showsPrec d (L _ e) = showsPrec d e

unLoc :: Located e -> e
unLoc (L _ e) = e

