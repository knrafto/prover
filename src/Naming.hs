{-# LANGUAGE OverloadedStrings #-}
module Naming
    ( Name(..)
    , resolveNames
    , Occurrence(..)
    , nameOccurrences
    )
where

import           Data.Aeson
import           Data.Text                      ( Text )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map

import           Location
import           Syntax

-- Identifier locations track where the name was introduced, not where it was used.
data Name
    = LocalName Ident
    | DefineName Ident
    | AssumeName Ident
    | UnboundName Text
    deriving (Show)

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

resolveExpr :: Env -> Expr Range Ident -> Expr Range Name
resolveExpr env expr = case expr of
    Hole l -> Hole l
    Var l ident ->
        let name = unLoc ident
        in  case () of
                _
                    | Just ident' <- Map.lookup name (envLocalNames env) -> Var
                        l
                        (LocalName ident')
                    | Just ident' <- Map.lookup name (envDefinitions env) -> Var
                        l
                        (DefineName ident')
                    | Just ident' <- Map.lookup name (envAssumptions env) -> Var
                        l
                        (AssumeName ident')
                    | otherwise -> Var l (UnboundName name)
    Type l      -> Type l
    Equal l x y -> Equal l (resolveExpr env x) (resolveExpr env y)
    Pi l ps e ->
        let (ps', env') = resolveParams env ps in Pi l ps' (resolveExpr env' e)
    Arrow l x y -> Arrow l (resolveExpr env x) (resolveExpr env y)
    Lam l ps e ->
        let (ps', env') = resolveParams env ps
        in  Lam l ps' (resolveExpr env' e)
    App l f xs -> App l (resolveExpr env f) (map (resolveExpr env) xs)
    Sigma l ps e ->
        let (ps', env') = resolveParams env ps
        in  Sigma l ps' (resolveExpr env' e)
    Times l x y -> Times l (resolveExpr env x) (resolveExpr env y)
    Tuple l xs  -> Tuple l (map (resolveExpr env) xs)

resolveParams :: Env -> [Param Range Ident] -> ([Param Range Name], Env)
resolveParams env [] = ([], env)
resolveParams env ((i, e) : rest) =
    let param = (i, resolveExpr env e)
        env' = env { envLocalNames = insertIdent i (envLocalNames env) }
        (params, env'') = resolveParams env' rest
    in  (param : params, env'')

resolveStatement :: Env -> Statement Range Ident -> (Statement Range Name, Env)
resolveStatement env stmt = case stmt of
    Define i ps ty body ->
        let (ps', env') = resolveParams env ps
        in  ( Define i ps' (fmap (resolveExpr env') ty) (resolveExpr env' body)
            , env { envDefinitions = insertIdent i (envDefinitions env) }
            )
    Assume i ty ->
        ( Assume i (resolveExpr env ty)
        , env { envAssumptions = insertIdent i (envAssumptions env) }
        )
    Prove i ty -> (Prove i (resolveExpr env ty), env)

resolveNames :: [Statement Range Ident] -> [Statement Range Name]
resolveNames = go emptyEnv
  where
    go _ [] = []
    go env (stmt : rest) =
        let (stmt', env') = resolveStatement env stmt in stmt' : go env' rest

-- A range and enum representing style information.
data Occurrence = Occurrence Range Name
    deriving (Show)

instance ToJSON Occurrence where
    toJSON (Occurrence l n) = object $ ["usage" .= l] ++ case n of
        LocalName i ->
            ["kind" .= ("local" :: Text), "introduction" .= location i]
        DefineName i ->
            ["kind" .= ("define" :: Text), "introduction" .= location i]
        AssumeName i ->
            ["kind" .= ("assume" :: Text), "introduction" .= location i]
        UnboundName _ -> ["kind" .= ("unbound" :: Text)]

-- TODO: DList?
exprOccurrences :: Expr Range Name -> [Occurrence]
exprOccurrences expr = case expr of
    Hole _        -> []
    Var l n       -> [Occurrence l n]
    Type _        -> []
    Equal _ x  y  -> exprOccurrences x ++ exprOccurrences y
    Pi    _ ps e  -> paramsOccurrences ps ++ exprOccurrences e
    Arrow _ x  y  -> exprOccurrences x ++ exprOccurrences y
    Lam   _ ps e  -> paramsOccurrences ps ++ exprOccurrences e
    App   _ f  xs -> exprOccurrences f ++ concatMap exprOccurrences xs
    Sigma _ ps e  -> paramsOccurrences ps ++ exprOccurrences e
    Times _ x  y  -> exprOccurrences x ++ exprOccurrences y
    Tuple _ xs    -> concatMap exprOccurrences xs

paramsOccurrences :: [Param Range Name] -> [Occurrence]
paramsOccurrences = concatMap $ \(i, ty) ->
    [Occurrence (location i) (LocalName i)] ++ exprOccurrences ty

nameOccurrences :: [Statement Range Name] -> [Occurrence]
nameOccurrences = concatMap $ \stmt -> case stmt of
    Define i ps ty body ->
        [Occurrence (location i) (DefineName i)]
            ++ paramsOccurrences ps
            ++ foldMap exprOccurrences ty
            ++ exprOccurrences body
    Assume i ty ->
        [Occurrence (location i) (AssumeName i)] ++ exprOccurrences ty
    Prove i ty ->
        [Occurrence (location i) (DefineName i)] ++ exprOccurrences ty
