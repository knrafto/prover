{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
module Naming
    ( NameKind(..)
    , Name(..)
    , N
    , resolveNames
    , extractNames
    )
where

import           Data.Foldable
import           Data.Maybe
import           Data.Text                      ( Text )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map

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
    { envLocalNames :: Map Text Ident
    , envDefinitions :: Map Text Ident
    , envAssumptions :: Map Text Ident
    }

emptyEnv :: Env
emptyEnv = Env { envLocalNames  = Map.empty
               , envDefinitions = Map.empty
               , envAssumptions = Map.empty
               }

insertIdent :: Ident -> Map Text Ident -> Map Text Ident
insertIdent ident = Map.insert (unLoc ident) ident

lookupIdent :: Env -> Ident -> Name
lookupIdent env ident = fromMaybe (Name Unbound ident ident) $ asum
    [ Name Local ident <$> Map.lookup name (envLocalNames env)
    , Name Defined ident <$> Map.lookup name (envDefinitions env)
    , Name Assumed ident <$> Map.lookup name (envAssumptions env)
    ]
    where name = unLoc ident

resolveExpr :: Env -> Expr P -> Expr N
resolveExpr env = \case
    Var l ident -> Var l (lookupIdent env ident)
    Type l      -> Type l
    Hole l      -> Hole l
    App l f a  -> App l (resolveExpr env f) (resolveExpr env a)
    Tuple l xs  -> Tuple l (map (resolveExpr env) xs)
    Pi l p e ->
        let (p', env') = resolveParam env p in Pi l p' (resolveExpr env' e)
    Lambda l p e ->
        let (p', env') = resolveParam env p
        in  Lambda l p' (resolveExpr env' e)
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

resolveNames :: [Statement P] -> [Statement N]
resolveNames = go emptyEnv
  where
    go _ [] = []
    go env (stmt : rest) =
        let (stmt', env') = resolveStatement env stmt in stmt' : go env' rest

-- TODO: DList?
exprNames :: Expr N -> [Name]
exprNames = \case
    Var _ n       -> [n]
    Hole _        -> []
    Type _        -> []
    App _ f a     -> exprNames f ++ exprNames a
    Tuple _ xs    -> concatMap exprNames xs
    Pi     _ p e -> paramNames p ++ exprNames e
    Lambda _ p e -> paramNames p ++ exprNames e
    Sigma  _ p e -> paramNames p ++ exprNames e
    Equal  _ x  y -> exprNames x ++ exprNames y
    Arrow  _ x  y -> exprNames x ++ exprNames y
    Times  _ x  y -> exprNames x ++ exprNames y

paramNames :: (Param N) -> [Name]
paramNames (n, ty) = n : foldMap exprNames ty

extractNames :: [Statement N] -> [Name]
extractNames = concatMap $ \stmt -> case stmt of
    Define n ty body -> n : (foldMap exprNames ty ++ exprNames body)
    Assume n ty -> n : exprNames ty
    Prove  n ty -> n : exprNames ty
