-- | Translates concrete syntax into abstract syntax, while generating
-- metavariables and type-checking constraints along the way. See Francesco
-- Mazzoli and Andreas Abel, "Type checking through unification",
-- https://arxiv.org/pdf/1609.09709v1.pdf.
module Prover.TypeCheck where

import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Text (Text)
import Prettyprinter

import Prover.Monad
import Prover.Pattern
import Prover.Pretty
import Prover.Syntax.Abstract qualified as A
import Prover.Syntax.Concrete qualified as C
import Prover.Syntax.Position
import Prover.Term
import Prover.Unify

-- | Create a metavariable with the given type in the given context.
createMeta :: Range -> Type -> M Term
createMeta r ty = do
  ctx <- asks envCtx
  id  <- freshMetaId
  -- Metavariables always represent closed terms, so in a context Γ we create
  -- a function Γ → A and apply it to all the variables in Γ.
  let metaTy = ctxPi ctx ty
  modify $ \s -> s
    { metaRanges = HashMap.insert id r (metaRanges s)
    , metaTypes = HashMap.insert id metaTy (metaTypes s)
    , unsolvedMetas = HashSet.insert id (unsolvedMetas s)
    }
  debugFields "create meta" $
    [ "loc"  |: return (pretty r)
    , "meta" |: return (prettyMeta id)
    , "ctx"  |: prettyCtx ctx
    , "type" |: prettyTerm ctx ty
    ]
  return $ BlockedMeta id (ctxVars ctx)

-- | Create a new name.
createName :: C.Name -> M A.Name
createName (C.Name r t) = do
  id <- freshNameId
  return (A.Name id r t)

-- | Add a param to the environment.
localParam :: A.Param -> M a -> M a
localParam p = local $ \e -> Env
  { envVarNames = Just (A.paramName p) : envVarNames e
  , envCtx      = envCtx e :> A.paramType p
  }

-- | Add a param group to the environment.
localParamGroup :: A.ParamGroup -> M a -> M a
localParamGroup (A.ParamGroup ps _) m = go ps
  where
    go [] = m
    go (p:ps) = localParam p $ go ps

-- | Add param groups to the environment.
localParams :: [A.ParamGroup] -> M a -> M a
localParams []     m = m
localParams (p:ps) m = localParamGroup p $ localParams ps m

-- | The number of variables in the parameter collection.
paramsLength :: [A.ParamGroup] -> Int
paramsLength = sum . map (\(A.ParamGroup ps _) -> length ps)

-- | Desugar parameters into a bunch of Π binders.
paramsPi :: [A.ParamGroup] -> Type -> Type
paramsPi [] ty = ty
paramsPi (A.ParamGroup ps _ : rest) ty = paramListPi ps $ paramsPi rest ty
  where
    paramListPi :: [A.Param] -> Type -> Type
    paramListPi [] ty  = ty
    paramListPi (p:ps) ty = Pi (A.paramType p) (paramListPi ps ty)

-- | Desugar parameters into a bunch of Σ binders.
paramsSigma :: [A.ParamGroup] -> Type -> Type
paramsSigma [] ty = ty
paramsSigma (A.ParamGroup ps _ : rest) ty = paramListSigma ps $ paramsSigma rest ty
  where
    paramListSigma :: [A.Param] -> Type -> Type
    paramListSigma [] ty  = ty
    paramListSigma (p:ps) ty = Sigma (A.paramType p) (paramListSigma ps ty)

-- | Desugar parameters into a bunch of λ binders.
paramsLam :: [A.ParamGroup] -> Term -> Term
paramsLam ps = makeLam (paramsLength ps)

-- | Add an unnamed param to the environment.
localUnnamed :: Type -> M a -> M a
localUnnamed ty = local $ \e -> Env
  { envVarNames = Nothing : envVarNames e
  , envCtx      = envCtx e :> ty
  }

-- | Lookup the de Bruijn index of a local variable name.
lookupLocal :: Text -> [Maybe A.Name] -> Maybe (Var, A.Name)
lookupLocal t varNames = go 0 varNames
  where
    go _ []               = Nothing
    go i (Just n:_)
      | A.nameText n == t = Just (i, n)
    go i (_:rest)         = go (i + 1) rest

-- | Generate a constraint that two terms (of possibly different types) are
-- equal.
addConstraint :: Range -> Term -> Type -> Term -> Type -> M ()
addConstraint r a tyA b tyB = do
  ctx <- asks envCtx
  debugFields "create constraint" $
    [ "loc" |: return (pretty r)
    , "ctx" |: prettyCtx ctx
    , "a"   |: prettyTerm ctx a
    , "A"   |: prettyTerm ctx tyA
    , "b"   |: prettyTerm ctx b
    , "B"   |: prettyTerm ctx tyB
    ]
  let c = Guarded (TermEq ctx Type tyA tyB) (TermEq ctx tyA a b)
  modify $ \s -> s { constraints = TopLevelConstraint r c : constraints s}

-- | Generate expression info for a range, term, and type, while checking that
-- it matches the expected output type.
expect :: Range -> Term -> Type -> Type -> M A.ExprInfo
expect r t ty expectedTy = do
  m <- createMeta r expectedTy
  addConstraint r m expectedTy t ty
  return (A.ExprInfo r m expectedTy)

-- | Apply a term to metavariables to fill implicit parameters.
expandImplicits :: Range -> Int -> Term -> Type -> M (Term, Type)
expandImplicits _ 0 t ty = return (t, ty)
expandImplicits r n t ty = do
  (a, b) <- case ty of
    Pi a b -> return (a, b)
    _ -> error "expandImplicits: not a Π-type"
  arg <- createMeta r a
  expandImplicits r (n - 1) (applyTerm t [arg]) (instantiate b arg)

-- | Producing a judgement Γ ⊢ t : A.
checkExpr :: C.Expr -> Type -> M A.Expr
checkExpr expr expectedTy = case expr of
  C.Id      n       -> do
    let r = C.nameRange n
        s = C.nameText n
    e <- ask
    state <- get
    case () of
      _ | Just (v, n) <- lookupLocal s (envVarNames e) -> do
          let t    = var v
              ty   = ctxLookup (envCtx e) v
              n'   = A.Name (A.nameId n) r s
          i <- expect r t ty expectedTy
          return $ A.Var i n'

      _ | Just id <- HashMap.lookup s (globalNames state)
        , Just ty <- HashMap.lookup id (defTypes state) -> do
          implicits <- getState id defImplicits
          t <- getState id defTerms
          let n' = A.Name id r s
          (t', ty') <- expandImplicits r implicits t ty
          i <- expect r t' ty' expectedTy
          return $ A.Def i n'

      _ | Just id <- HashMap.lookup s (globalNames state)
        , Just ty <- HashMap.lookup id (axiomTypes state) -> do
          implicits <- getState id axiomImplicits
          let n' = A.Name id r s
              t  = BlockedAxiom id []
          (t', ty') <- expandImplicits r implicits t ty
          i <- expect r t' ty' expectedTy
          return $ A.Axiom i n'

      _ -> do
        emitError $ UnboundName r s
        t <- createMeta r expectedTy
        return $ A.Unbound (A.ExprInfo r t expectedTy) s

  C.Hole    r       -> do
    t <- createMeta r expectedTy
    return $ A.Hole (A.ExprInfo r t expectedTy)

  C.Type    r       -> do
    i <- expect r Type Type expectedTy
    return $ A.Type i

  C.Pi      r ps e  -> do
    -- Γ ⊢ A : Type
    ps' <- checkParams ps

    -- Γ, x : A ⊢ B : Type
    e' <- localParams ps' $ checkExpr e Type

    -- ⟹ Γ ⊢ (Π x : A. B) : Type
    let t = paramsPi ps' (A.exprTerm e')
    i <- expect r t Type expectedTy
    return $ A.Pi i ps' e'

  C.Lam     r ps e  -> do
    -- Γ ⊢ A : Type
    ps' <- checkParams ps

    -- Γ, x : A ⊢ e : B
    tyB <- localParams ps'  $ createMeta r Type
    e'  <- localParams ps' $ checkExpr e tyB

    -- ⟹ Γ ⊢ (λ x : A. e) : (Π x : A. B)
    let t   = paramsLam ps' (A.exprTerm e')
        ty  = paramsPi ps' (A.exprType e')
    i <- expect r t ty expectedTy
    return $ A.Lam i ps' e'

  C.Sigma   r ps e  -> do
    -- Γ ⊢ A : Type
    ps' <- checkParams ps

    -- Γ, x : A ⊢ B : Type
    e' <- localParams ps' $ checkExpr e Type

    -- ⟹ Γ ⊢ (Σ x : A. B) : Type
    let t = paramsSigma ps' (A.exprTerm e')
    i <- expect r t Type expectedTy
    return $ A.Sigma i ps' e'

  C.App     r f a   -> do
    -- Γ ⊢ a : A
    tyA <- createMeta r Type
    a'  <- checkExpr a tyA

    -- Γ ⊢ f : (Π x : A. B)
    tyB <- localUnnamed tyA $ createMeta r Type
    f'  <- checkExpr f (Pi tyA tyB)

    -- ⟹ Γ ⊢ f a : B[a/x]
    -- TODO: a chained application is currently quadratic in the number of
    -- arguments
    let t  = applyTerm (A.exprTerm f') [A.exprTerm a']
        ty = instantiate tyB (A.exprTerm a') 
    i <- expect r t ty expectedTy
    return $ A.App i f' a'

  C.Arrow   r e1 e2 ->  do
    -- Γ ⊢ A : Type
    e1' <- checkExpr e1 Type

    -- Γ ⊢ B : Type
    e2' <- checkExpr e2 Type

    -- ⟹ Γ ⊢ (Π _ : A. B) : Type
    let t = Pi (A.exprTerm e1') (weaken (A.exprTerm e2'))
    i <- expect r t Type expectedTy
    return $ A.Arrow i e1' e2'

  C.Times   r e1  e2  -> do
    -- Γ ⊢ A : Type
    e1' <- checkExpr e1 Type

    -- Γ ⊢ B : Type
    e2' <- checkExpr e2 Type

    -- ⟹ Γ ⊢ (Σ _ : A. B) : Type
    let t = Sigma (A.exprTerm e1') (weaken (A.exprTerm e2'))
    i <- expect r t Type expectedTy
    return $ A.Times i e1' e2'

  C.Equals  r e1 e2 -> do
    -- Desugar a = b to Id (_ : Type) a b
    -- TODO: check type of Id is correct! 
    id  <- lookupState "Id" globalNames >>= \case
      Nothing -> error "missing builtin Id"
      Just id -> return id
    tyA <- createMeta r Type
    e1' <- checkExpr e1 tyA
    e2' <- checkExpr e2 tyA
    let t   = BlockedAxiom id [tyA, A.exprTerm e1', A.exprTerm e2']
    i <- expect r t Type expectedTy
    return $ A.Equals i e1' e2'

  C.Pair    _ _  _  -> error "pair"

-- | Given (x : A), check Γ ⊢ A : Type and construct a param for x.
checkParamNames :: [C.Name] -> Type -> M [A.Param]
checkParamNames [] _ = return []
checkParamNames (n:ns) ty = do
  n' <- createName n
  let p = A.Param n' ty
  ps <- localParam p $ checkParamNames ns (weaken ty)
  return (p:ps)

-- | Given (x : A), check Γ ⊢ A : Type and construct a param for x.
checkParamGroup :: C.ParamGroup -> M A.ParamGroup
checkParamGroup (C.ParamGroup ns ann) = do
  (ty', ann') <- case ann of
    Nothing -> do
      -- TODO: is this the right range? or should it be all of them?
      ty <- createMeta (C.nameRange (head ns)) Type
      return (ty, Nothing)
    Just ty -> do
      ty' <- checkExpr ty Type
      return (A.exprTerm ty', Just ty')
  ps <- checkParamNames ns ty'
  return $ A.ParamGroup ps ann'

checkParams :: [C.ParamGroup] -> M [A.ParamGroup]
checkParams [] = return []
checkParams (p:ps) = do
  p' <- checkParamGroup p
  ps' <- localParamGroup p' $ checkParams ps
  return (p':ps')

termToPattern :: Term -> MaybeT M Pattern
termToPattern t = lift (whnf t) >>= \case
  Var i []     -> return (VarPat i)
  Axiom i args -> AxiomPat i <$> mapM termToPattern args
  _            -> mzero

checkDecl :: C.Decl -> M A.Decl
checkDecl = \case
  C.Define n implicits explicits ann e -> do
    debug $ "checking definition" <+> pretty (C.nameText n) <+> "..."
    params' <- checkParams (implicits ++ explicits)
    (def, ann', e') <- localParams params' $ do
      n' <- createName n
      (ty, ann') <- case ann of
        Nothing -> do
          ty <- createMeta (A.nameRange n') Type
          return (ty, Nothing)
        Just ann -> do
          ann' <- checkExpr ann Type
          return (A.exprTerm ann', Just ann')
      e' <- checkExpr e ty
      return (A.Param n' ty, ann', e')
    solveConstraints
    let n' = A.paramName def
        ty = paramsPi params' (A.exprType e')
        tm = paramsLam params' (A.exprTerm e')
    modify $ \s -> s
      { globalNames  = HashMap.insert (A.nameText n') (A.nameId n') (globalNames s)
      , defNames     = HashMap.insert (A.nameId n') n' (defNames s)
      , defImplicits = HashMap.insert (A.nameId n') (length implicits) (defImplicits s)
      , defTypes     = HashMap.insert (A.nameId n') ty (defTypes s)
      , defTerms     = HashMap.insert (A.nameId n') tm (defTerms s)
      }
    return $ A.Define params' def ann' e'
  C.Assume n implicits explicits ann -> do
    debug $ "checking axiom" <+> pretty (C.nameText n) <+> "..."
    params' <- checkParams (implicits ++ explicits)
    (ctx, def, ann') <- localParams params' $ do
      ctx <- asks envCtx
      n' <- createName n
      ann' <- checkExpr ann Type
      let ty = A.exprTerm ann'
      return (ctx, A.Param n' ty, ann')
    solveConstraints
    let n' = A.paramName def
        ty = ctxPi ctx (A.paramType def)
    modify $ \s -> s
      { globalNames    = HashMap.insert (A.nameText n') (A.nameId n') (globalNames s)
      , axiomNames     = HashMap.insert (A.nameId n') n' (axiomNames s)
      , axiomImplicits = HashMap.insert (A.nameId n') (length implicits) (axiomImplicits s)
      , axiomTypes     = HashMap.insert (A.nameId n') ty (axiomTypes s)
      }
    return $ A.Assume params' def ann'
  C.Rewrite n params lhs rhs -> do
    debug $ "checking rewrite" <+> pretty (C.nameText n) <+> "..."
    params' <- checkParams params
    (def, lhs', rhs') <- localParams params' $ do
      n' <- createName n
      ty <- createMeta (A.nameRange n') Type
      lhs' <- checkExpr lhs ty
      rhs' <- checkExpr rhs ty
      return (A.Param n' ty, lhs', rhs')
    solveConstraints
    runMaybeT (termToPattern (A.exprTerm lhs')) >>= \case
      Just (AxiomPat h args) -> do
        let rule = Rule
              { ruleCtxLength = paramsLength params'
              , ruleHead      = h
              , ruleArgs      = args
              , ruleRhs       = paramsLam params' (A.exprTerm rhs')
              }
        if matchable rule then
          -- TODO: validate is matchable
          modify $ \s -> s
            { axiomRules = HashMap.insertWith (++) (ruleHead rule) [rule] (axiomRules s)
            }
        else
          emitError $ MissingPatternVariable (getRange lhs')
      _ -> emitError $ BadPattern (getRange lhs')
    return $ A.Rewrite params' def lhs' rhs'
  C.Fixity fixity i n -> do
    return $ A.Fixity fixity i (C.nameText n)

checkModule :: C.Module -> M A.Module
checkModule (C.Module decls) = A.Module <$> mapM checkDecl decls
