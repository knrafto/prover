module NewTerm where

newtype MetaId = MetaId Int
    deriving (Eq, Ord)

data Head
    -- De Bruijn bound variable.
    = Var {-# UNPACK #-} !Int
    | Meta {-# UNPACK #-} !MetaId

-- Core term representation. Terms are always well-typed.
data Term
    = App !Head [Term]  -- Neutral application.
    | Lam !Term
    | Universe
    | Pi !Term !Term
