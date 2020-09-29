-- | Syntax that has been typed-checked. This syntax still represents what the
-- user wrote, but it has been annotated with lots of information that proves it
-- is "correct". For example, every expression is annotated with a term and
-- type, and overloaded names have been resolved.
module Prover.Syntax.Abstract where

import Data.Text (Text)

import Prover.Syntax.Position
import Prover.Term (NameId, Term, Type)

-- | An occurence of a name.
data Name = Name
  { -- | Unique identifier for the thing that this name refers to. All names
    -- that refer to the same binding site have the same nameId.
    nameId          :: NameId
    -- | Where this name was used.
  , nameRange       :: Range
    -- | The spelling of this name.
  , nameText        :: Text
  } deriving (Show)

instance HasRange Name where
  getRange = nameRange

data ExprInfo = ExprInfo
  { -- | The location of the expression.
    exprInfoRange :: Range
    -- | The inferred term that this expression represents.
  , exprInfoTerm  :: Term
    -- | The inferred type of the term that this expression represents.
  , exprInfoType  :: Type
  } deriving (Show)

instance HasRange ExprInfo where
  getRange = exprInfoRange

data Expr
  = Var     ExprInfo Name  -- ^ A bound variable.
  | Def     ExprInfo Name  -- ^ A defined name.
  | Axiom   ExprInfo Name  -- ^ An axiom name.
  | Unbound ExprInfo Text  -- ^ An unbound name.
  | Hole    ExprInfo       -- ^ An underscore hole.
  | Type    ExprInfo
  | Pi      ExprInfo [ParamGroup] Expr
  | Lam     ExprInfo [ParamGroup] Expr
  | Sigma   ExprInfo [ParamGroup] Expr
  | App     ExprInfo Expr Expr
  | Arrow   ExprInfo Expr Expr
  | Times   ExprInfo Expr Expr
  | Equals  ExprInfo Expr Expr
  | Pair    ExprInfo Expr Expr
  deriving (Show)

exprInfo :: Expr -> ExprInfo
exprInfo = \case
  Var     i _   -> i
  Def     i _   -> i
  Axiom   i _   -> i
  Unbound i _   -> i
  Hole    i     -> i
  Type    i     -> i
  Pi      i _ _ -> i
  Lam     i _ _ -> i
  Sigma   i _ _ -> i
  App     i _ _ -> i
  Arrow   i _ _ -> i
  Times   i _ _ -> i
  Equals  i _ _ -> i
  Pair    i _ _ -> i

instance HasRange Expr where
  getRange = exprInfoRange . exprInfo

exprTerm :: Expr -> Term
exprTerm = exprInfoTerm . exprInfo

exprType :: Expr -> Type
exprType = exprInfoType . exprInfo

-- | A name that was optionally annotated with a type by the user (but we know
-- the type now).
data Param = Param
  { paramName :: Name
  , paramType :: Type
  } deriving (Show)

instance HasRange Param where
  -- TODO: store full range including annotation (and parens)?
  getRange = getRange . paramName

data ParamGroup = ParamGroup [Param] (Maybe Expr)
  deriving (Show)

-- TODO: it doesn't really make sense to use Param for the actual name?
data Decl
  = Define [ParamGroup] Param (Maybe Expr) Expr
  | Assume [ParamGroup] Param Expr
  | Rewrite [ParamGroup] Param Expr Expr
  deriving (Show)

newtype Module = Module [Decl]
  deriving (Show)
