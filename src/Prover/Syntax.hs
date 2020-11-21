-- | Syntax trees are parameterized by:
--
-- * A type `a` of "annotations" for expressions. After parsing, the annotation
--   records to source range of the expression. After type-checking, the
--   annotation records the type and term of every expression.
-- * A type `n` of "names". After parsing, names are simply strings. After
--   type-checking, names have types and information about what they refer to.
module Prover.Syntax where

import Data.Text (Text)

import Prover.Position hiding (Fixity)
import Prover.Term (NameId, Type, Term)

-- | A name that has not yet been resolved.
-- TODO: is there a better name for this than "Ident"?
data Ident = Ident
  {
    -- | Where this identifier was used.
    identRange :: Range
    -- | The spelling of this identifier.
  , identText :: Text
  } deriving (Show)

-- | The thing (local variable, definition, or axiom) that a name refers to.
-- Names are "unbound" if they don't refer to anything in scope.
data NameReferent
  = Local !NameId
  | Def !NameId
  | Axiom !NameId
  | Unbound
  deriving (Show)

-- | An occurence of a name.
data Name = Name
  {
    -- | Where this name was used.
    nameRange :: Range
    -- | The spelling of this name.
  , nameText :: Text
    -- | The thing this name refers to.
  , nameReferent :: NameReferent
    -- | The type of this name.
  , nameType :: Type
  } deriving (Show)

-- | Type-checking information about an expression.
data ExprInfo = ExprInfo
  { -- | The location of the expression.
    exprInfoRange :: Range
    -- | The inferred term that this expression represents.
  , exprInfoTerm :: Term
    -- | The inferred type of the term that this expression represents.
  , exprInfoType :: Type
  } deriving (Show)

-- | An expression.
data Expr a n
  -- | A variable.
  = Var a n
  -- | A hole `_`.
  | Hole a
  -- | `Type`.
  | Type a
  -- | `Π`.
  | Pi a [ParamGroup a n] (Expr a n)
  -- | `λ`.
  | Lam a [ParamGroup a n] (Expr a n)
  -- | `Σ`.
  | Sigma a [ParamGroup a n] (Expr a n)
  -- | A sequence of terms (possibly involving infix operators) that must be
  -- parsed into applications.
  | Apps a [Expr a n]
  -- | A function application.
  | App a (Expr a n) (Expr a n)
  -- | `→`.
  | Arrow a (Expr a n) (Expr a n)
  -- | A pair `(a, b)`.
  | Pair a (Expr a n) (Expr a n)
  deriving (Show)

-- | Extract the annotation from an expression.
ann :: Expr a n -> a
ann = \case
  Var   a _   -> a
  Hole  a     -> a
  Type  a     -> a
  Pi    a _ _ -> a
  Lam   a _ _ -> a
  Sigma a _ _ -> a
  Apps  a _   -> a
  App   a _ _ -> a
  Arrow a _ _ -> a
  Pair  a _ _ -> a

-- | A list of a names with an optional type annotation.
data ParamGroup a n = ParamGroup [n] (Maybe (Expr a n))
  deriving (Show)

-- | A kind of infix-ness.
data Fixity = Infix | Infixl | Infixr
  deriving (Eq, Show)

-- | A top-level declaration.
data Decl a n
  = Define n [ParamGroup a n] [ParamGroup a n] (Maybe (Expr a n)) (Expr a n)
  | Assume n [ParamGroup a n] [ParamGroup a n] (Expr a n)
  | Rewrite n [ParamGroup a n] (Expr a n) (Expr a n)
  | Fixity Fixity Int Text
  deriving (Show)

-- | A source module, which is simply a list of declarations.
newtype Module a n = Module [Decl a n]
  deriving (Show)
