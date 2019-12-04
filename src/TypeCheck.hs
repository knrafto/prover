{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module TypeCheck where

import           Data.List

import           Control.Monad.State
import qualified Data.Map.Strict               as Map
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text

import           Location
import           Naming
import           TcM
import           Term
import           Syntax                         ( Id
                                                , Ann
                                                , ann
                                                , Expr
                                                , Param
                                                , Statement
                                                )
import qualified Syntax

-- A term annotated with a type, used for type-checking and unification.
type UTerm = (Term, Type)
data TcAnn = TcAnn !Range !UTerm

data Tc
type instance Id Tc = Name
type instance Ann Tc = TcAnn

exprUTerm :: Expr Tc -> UTerm
exprUTerm e = case ann e of
    TcAnn _ tt -> tt

exprTerm :: Expr Tc -> Term
exprTerm e = case ann e of
    TcAnn _ (t, _) -> t

exprType :: Expr Tc -> Type
exprType e = case ann e of
    TcAnn _ (_, ty) -> ty

typeCheck :: [Statement N] -> TcM [Statement Tc]
typeCheck = mapM typeCheckStatement

typeCheckStatement :: Statement N -> TcM (Statement Tc)
typeCheckStatement = \case
    Syntax.Define n mty body -> do
        let name = unLoc (nameUsage n)
        body' <- typeCheckExpr C0 [] body
        mty' <- case mty of
            Nothing -> return Nothing
            Just ty -> do
                ty' <- typeCheckExpr C0 [] ty
                unify C0 Universe (exprType body') (exprTerm ty')
                return (Just ty')
        checkSolved
        modify $ \s -> s { tcDefinitions = Map.insert name (exprUTerm body') (tcDefinitions s) }
        return (Syntax.Define n mty' body')
    Syntax.Assume n ty -> do
        let name = unLoc (nameUsage n)
        ty' <- typeCheckExpr C0 [] ty
        checkSolved
        modify $ \s -> s { tcAssumptions = Map.insert name (exprTerm ty') (tcAssumptions s) }
        return (Syntax.Assume n ty')
    Syntax.Prove _ _ -> fail "prove not implemented"

typeCheckExpr :: Ctx -> [Text] -> Expr N -> TcM (Expr Tc)
typeCheckExpr ctx names = \case
    Syntax.Var l n -> do
        let name = unLoc (nameUsage n)
        -- We assume that name resolution is correct so that the map lookups cannot fail.
        tt <- case nameKind n of
            Local -> do
                let Just i = elemIndex name names
                return (Var i [], ctxVarType ctx i)
            Defined -> do
                definitions <- gets tcDefinitions
                let Just (t, ty) = Map.lookup name definitions
                return (t, ty)
            Assumed -> assumption name
            Unbound -> fail $ "unbound name: " ++ Text.unpack name
        return (Syntax.Var (TcAnn l tt) n)
    Syntax.Hole l -> do
        tt <- hole ctx
        return (Syntax.Hole (TcAnn l tt))
    Syntax.Type l -> return (Syntax.Type (TcAnn l (Universe, Universe)))
    Syntax.App l f arg -> do
        f'    <- typeCheckExpr ctx names f
        arg'  <- typeCheckExpr ctx names arg
        tt    <- typeCheckApp ctx (exprUTerm f') (exprUTerm arg')
        return (Syntax.App (TcAnn l tt) f' arg')
    Syntax.Tuple l args -> do
        args' <- mapM (typeCheckExpr ctx names) args
        tt    <- typeCheckTuple ctx (map exprUTerm args')
        return (Syntax.Tuple (TcAnn l tt) args')
    Syntax.Pi l param body -> do
        (param', paramTerm, body') <- typeCheckParam ctx names param body
        tt <- typeCheckPi ctx paramTerm (exprUTerm body')
        return (Syntax.Pi (TcAnn l tt) param' body')
    Syntax.Lambda l param body -> do
        (param', paramTerm, body') <- typeCheckParam ctx names param body
        tt <- typeCheckLambda ctx paramTerm (exprUTerm body')
        return (Syntax.Lambda (TcAnn l tt) param' body')
    Syntax.Sigma  l param body -> do
        (param', paramTerm, body') <- typeCheckParam ctx names param body
        tt <- typeCheckSigma ctx paramTerm (exprUTerm body')
        return (Syntax.Sigma (TcAnn l tt) param' body')
    Syntax.Equal  l a      b  -> do
        f <- assumption "Id"
        _A <- hole ctx
        a' <- typeCheckExpr ctx names a
        b' <- typeCheckExpr ctx names b
        tt <- typeCheckApps ctx f [_A, exprUTerm a', exprUTerm b']
        return (Syntax.Equal (TcAnn l tt) a' b')
    Syntax.Arrow l a b -> do
        a' <- typeCheckExpr ctx names a
        b' <- typeCheckExpr ctx names b
        tt <- typeCheckPi ctx (exprUTerm a') (weakenUTerm (exprUTerm b'))
        return (Syntax.Arrow (TcAnn l tt) a' b')
    Syntax.Times l a b -> do
        a' <- typeCheckExpr ctx names a
        b' <- typeCheckExpr ctx names b
        tt <- typeCheckSigma ctx (exprUTerm a') (weakenUTerm (exprUTerm b'))
        return (Syntax.Times (TcAnn l tt) a' b')

assumption :: Text -> TcM UTerm
assumption name = do
    assumptions <- gets tcAssumptions
    case Map.lookup name assumptions of
        Just _A -> return (Assumption name [], _A)
        _       -> fail $ "can't find built-in: " ++ Text.unpack name

-- Generate an unknown term and type.
hole :: Ctx -> TcM UTerm
hole _Γ = do
    -- We generate variables for both the hole itself, and its type. Luckily
    -- for now we don't have to do this forever, since the type of any type is
    -- the universe.
    ty <- freshMeta' _Γ Universe
    t <- freshMeta' _Γ ty
    return (t, ty)

weakenUTerm :: UTerm -> UTerm
weakenUTerm (t, ty) = (weaken t, weaken ty)

typeCheckParam :: Ctx -> [Text] -> Param N -> Expr N -> TcM (Param Tc, UTerm, Expr Tc)
typeCheckParam ctx names (n, me) body = do
    let name = unLoc (nameUsage n)
    (me', tt) <- case me of
        Nothing -> do
            tt <- hole ctx
            return (Nothing, tt)
        Just e -> do
            e' <- typeCheckExpr ctx names e
            return (Just e', exprUTerm e')
    body' <- typeCheckExpr (ctx :> (fst tt)) (name : names) body
    return ((n, me'), tt, body')

typeCheckPi :: Ctx -> UTerm -> UTerm -> TcM UTerm
typeCheckPi ctx (_A, _Aty) (_B, _Bty) = do
    unify ctx Universe _Aty Universe
    unify (ctx :> _A) Universe _Bty Universe
    return (Pi _A _B, Universe)

typeCheckLambda :: Ctx -> UTerm -> UTerm -> TcM UTerm
typeCheckLambda ctx (_A, _Aty) (b, _B) = do
    unify ctx Universe _Aty Universe
    return (Lam b, Pi _A _B)

typeCheckSigma :: Ctx -> UTerm -> UTerm -> TcM UTerm
typeCheckSigma ctx a b = do
    f  <- assumption "Σ'"
    b' <- typeCheckLambda ctx a b
    typeCheckApps ctx f [a, b']

typeCheckApp :: Ctx -> UTerm -> UTerm -> TcM UTerm
typeCheckApp ctx (f, fty) (arg, _A) = do
    _B <- freshMeta' (ctx :> _A) Universe
    unify ctx Universe fty (Pi _A _B)
    return (app f [arg], instantiate _B arg)

typeCheckApps :: Ctx -> UTerm -> [UTerm] -> TcM UTerm
typeCheckApps _   f []           = return f
typeCheckApps ctx f (arg : args) = do
    f' <- typeCheckApp ctx f arg
    typeCheckApps ctx f' args

typeCheckTuple :: Ctx -> [UTerm] -> TcM UTerm
typeCheckTuple _   []         = error "typeCheckTuple: empty tuple"
typeCheckTuple _   [t       ] = return t
typeCheckTuple ctx (a : rest) = do
    _A   <- hole ctx
    _B   <- hole ctx
    b    <- typeCheckTuple ctx rest
    pair <- assumption "pair"
    typeCheckApps ctx pair [_A, _B, a, b]

printStatements :: [Statement Tc] -> IO ()
printStatements = mapM_ printStatement

printStatement :: Statement Tc -> IO ()
printStatement = \case
    Syntax.Define n _ body -> do
        let name = unLoc (nameUsage n)
        putStrLn $ "define " ++ Text.unpack name ++ " := " ++ show (exprTerm body)
    Syntax.Assume n ty -> do
        let name = unLoc (nameUsage n)
        putStrLn $ "assume " ++ Text.unpack name ++ " : " ++ show (exprTerm ty)
    Syntax.Prove _ _ -> fail "prove not implemented"
