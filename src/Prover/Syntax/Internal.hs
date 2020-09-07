-- | The syntax of the raw type theory.
module Prover.Syntax.Internal where

import Data.Hashable

-- | A de Bruijn index.
newtype Var = V Int
  deriving (Eq, Show)

-- | A unique identifier for a thing with a name, used to determine if two names
-- refer to "the same thing", or two different things with the same name.
newtype NameId = NameId Int
  deriving (Eq, Ord, Show, Enum, Hashable)

-- | A unique identifier for a metavariable.
newtype MetaId = MetaId Int
  deriving (Eq, Ord, Show, Enum, Hashable)

-- | The head of a neutral term.
data Head
  -- | A local variable (as a de Bruijn index).
  = Var !Var
  -- | A defined name.
  | Def !NameId
  -- | An assumed name.
  | Axiom !NameId
  -- | A metavariable.
  | Meta !MetaId
  deriving (Show)

-- | A term in some context of some type. Terms are kept in
-- almost-but-not-quite-normal form. The term can only be reduced by
-- substituting for the head of a neutral term.
data Term
  -- | A neutral term application.
  = App !Head [Term]
  -- | A universe.
  | Type
  -- | A Π-type.
  | Pi Type (Abs Type)
  -- | A lambda function.
  | Lam (Abs Term)
  deriving (Show)

-- | A type, represented by terms in a universe.
-- TODO: universe levels
newtype Type = El Term
  deriving (Show)

-- | The body of a binder (Π or λ). This type is mostly so we're careful when
-- juggling de Bruijn indices.
newtype Abs t = Abs t
  deriving (Show)

-- | A context for a term.
data Ctx
  = C0
  | !Ctx :< Type
  deriving (Show)
