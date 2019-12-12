{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
-- Scope-checking, i.e. name resolution.
module ScopeCheck
    ( NameKind(..)
    , Name(..)
    , N
    , scopeCheck
    )
where

import           Data.Foldable
import           Data.Maybe
import           Data.Text                      ( Text )
import           Data.HashMap.Strict            ( HashMap )
import qualified Data.HashMap.Strict           as HashMap

import           Location
import           Parser
import           Syntax

data NameKind
    -- Introduced via a binder
    = Local
    -- A symbol from a `define`
    | Defined
    -- A symbol from an `assume`
    | Assumed
    -- An unknown symbol
    | Unbound
    deriving (Eq, Show)

-- An occurrence of an identifier.
data Name = Name
    { nameKind :: NameKind
    , nameUsage :: Ident
    , nameIntroduction :: Ident
    }
    deriving (Eq, Show)

data N
type instance Id N = Name
type instance Ann N = Range

data Env = Env
    { envLocalNames :: HashMap Text Ident
    , envDefinitions :: HashMap Text Ident
    , envAssumptions :: HashMap Text Ident
    }

emptyEnv :: Env
emptyEnv = Env { envLocalNames  = HashMap.empty
               , envDefinitions = HashMap.empty
               , envAssumptions = HashMap.empty
               }

insertIdent :: Ident -> HashMap Text Ident -> HashMap Text Ident
insertIdent ident = HashMap.insert (identText ident) ident

lookupIdent :: Env -> Ident -> Name
lookupIdent env ident = fromMaybe (Name Unbound ident ident) $ asum
    [ Name Local ident <$> HashMap.lookup name (envLocalNames env)
    , Name Defined ident <$> HashMap.lookup name (envDefinitions env)
    , Name Assumed ident <$> HashMap.lookup name (envAssumptions env)
    ]
    where name = identText ident

resolveExpr :: Env -> Expr P -> Expr N
resolveExpr env = \case
    Var l ident -> Var l (lookupIdent env ident)
    Type l      -> Type l
    Hole l      -> Hole l
    App l f a  -> App l (resolveExpr env f) (resolveExpr env a)
    Tuple l xs  -> Tuple l (map (resolveExpr env) xs)
    Pi l p e ->
        let (p', env') = resolveParam env p in Pi l p' (resolveExpr env' e)
    Lam l p e ->
        let (p', env') = resolveParam env p
        in  Lam l p' (resolveExpr env' e)
    Sigma l p e ->
        let (p', env') = resolveParam env p
        in  Sigma l p' (resolveExpr env' e)
    Equal l x y -> Equal l (resolveExpr env x) (resolveExpr env y)
    Arrow l x y -> Arrow l (resolveExpr env x) (resolveExpr env y)
    Times l x y -> Times l (resolveExpr env x) (resolveExpr env y)

resolveParam :: Env -> (Param P) -> (Param N, Env)
resolveParam env (i, e) =
    let param = (Name Local i i, fmap (resolveExpr env) e)
        env' = env { envLocalNames = insertIdent i (envLocalNames env) }
    in  (param, env')

resolveStatement :: Env -> Statement P -> (Statement N, Env)
resolveStatement env = \case
    Define i ty body ->
        ( Define (Name Defined i i)
                     (fmap (resolveExpr env) ty)
                     (resolveExpr env body)
        , env { envDefinitions = insertIdent i (envDefinitions env) }
        )
    Assume i ty ->
        ( Assume (Name Assumed i i) (resolveExpr env ty)
        , env { envAssumptions = insertIdent i (envAssumptions env) }
        )
    Prove i ty -> (Prove (Name Defined i i) (resolveExpr env ty), env)

scopeCheck :: [Statement P] -> [Statement N]
scopeCheck = go emptyEnv
  where
    go _ [] = []
    go env (stmt : rest) =
        let (stmt', env') = resolveStatement env stmt in stmt' : go env' rest
