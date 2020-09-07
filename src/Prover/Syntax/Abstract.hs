-- | Syntax that has been typed-checked. This syntax still represents what the
-- user wrote, but it has been annotated with lots of information that proves it
-- is "correct". For example, every expression is annotated with a term and
-- type, and overloaded names have been resolved.
module Prover.Syntax.Abstract where

import Data.Text (Text)

import Prover.Syntax.Internal
import Prover.Syntax.Position

-- | An occurence of a name.
data Name = Name
  { -- | Unique identifier for the thing that this name refers to. All names
    -- that refer to the same binding site have the same nameId.
    nameId          :: NameId
    -- | The spelling of this name.
  , nameText        :: Text
    -- | Where this name was used.
  , nameRange       :: Range
  } deriving (Show)

data ExprInfo = ExprInfo
  { -- | The location of the expression.
    exprRange :: Range
    -- | The inferred term that this expression represents.
  , exprTerm  :: Term
    -- | The inferred type of the term that this expression represents.
  , exprType  :: Type
  } deriving (Show)

data Expr
  = Var     ExprInfo Name  -- ^ A bound variable.
  | Def     ExprInfo Name  -- ^ A defined name.
  | Axiom   ExprInfo Name  -- ^ An assumed name.
  | Hole    ExprInfo       -- ^ An underscore hole.
  | Type    ExprInfo
  | Pi      ExprInfo Binding Expr
  | Lam     ExprInfo Binding Expr
  | Sigma   ExprInfo Binding Expr
  | App     ExprInfo Expr Expr
  | Arrow   ExprInfo Expr Expr
  | Times   ExprInfo Expr Expr
  | Equals  ExprInfo Expr Expr
  | Pair    ExprInfo Expr Expr
  deriving (Show)

-- | A name that was optionally annotated with a type by the user (but we know
-- the type now).
data Binding = Binding
  { bindingName       :: Name
  , bindingType       :: Type
  , bindingAnnotation :: Maybe Expr
  } deriving (Show)

data Decl
  = Define Binding Expr
  | Assume Binding
  deriving (Show)

newtype Module = Module [Decl]
  deriving (Show)
