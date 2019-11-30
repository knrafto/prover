{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module NewTerm where

import           Data.Hashable
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as H
import           Data.Text           (Text)

import           Location

newtype MetaId = MetaId Int
    deriving (Eq, Hashable)

-- Core term representation. Terms are always well-typed.
data Term
    = Var {-# UNPACK #-} !Int [Term]
    | Meta {-# UNPACK #-} !MetaId [Term]
    | Lam !Term
    | Universe
    | Pi !Type !Type

type Type = Term

-- A context, with named variables.
data Ctx
    = EmptyCtx
    | ExtendCtx !Ctx !Ident !Type

-- Construct a Π-type out of a context ending with the given type.
ctxPi :: Ctx -> Type -> Type
ctxPi EmptyCtx t = t
ctxPi (ExtendCtx ctx _ ty) t = ctxPi ctx (Pi ty t)

-- Construct a lambda out of a context with the given body.
ctxLam :: Ctx -> Term -> Term
ctxLam EmptyCtx t = t
ctxLam (ExtendCtx ctx _ _) t = ctxLam ctx (Lam t)

-- A collection of globally-scoped things.
data Signature = Signature
    -- Global definitions, and their values and types.
    { sigDefinitions :: HashMap Text (Term, Type)
    -- Global assumptions, and their types.
    , sigAssumptions :: HashMap Text Type
    -- Next metavar id.
    , sigNextId :: !Int
    -- Metavar types.
    , sigMetaTypes :: HashMap MetaId Type
    -- Metavar substitution.
    , sigMetaValues :: HashMap MetaId Type
    }

emptySignature :: Signature
emptySignature = Signature
    { sigDefinitions = H.empty
    , sigAssumptions = H.empty
    , sigNextId = 0
    , sigMetaTypes = H.empty
    , sigMetaValues = H.empty
    }

newMeta :: Type -> Signature -> (MetaId, Signature)
newMeta ty sig = (MetaId i, sig')
  where
    i = sigNextId sig
    sig' = sig
        { sigNextId = i + 1
        , sigMetaTypes = H.insert (MetaId i) ty (sigMetaTypes sig)
        }
