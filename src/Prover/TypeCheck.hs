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
import Prover.Syntax.Internal
import Prover.Syntax.Position
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
  return $ App (Meta id) (ctxVars ctx)

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

-- | Add a param to the environment.
localParams :: [A.Param] -> M a -> M a
localParams []     m = m
localParams (p:ps) m = localParam p $ localParams ps m

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
          let t    = App (Var v) []
              ty   = ctxLookup (envCtx e) v
              n'   = A.Name (A.nameId n) r s
          i <- expect r t ty expectedTy
          return $ A.Var i n'

      _ | Just id <- HashMap.lookup s (globalNames state)
        , Just ty <- HashMap.lookup id (defTypes state) -> do
          let t    = App (Def id) []
              n'   = A.Name id r s
          i <- expect r t ty expectedTy
          return $ A.Def i n'

      _ | Just id <- HashMap.lookup s (globalNames state)
        , Just ty <- HashMap.lookup id (axiomTypes state) -> do
          let t    = App (Axiom id) []
              n'   = A.Name id r s
          i <- expect r t ty expectedTy
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

  C.Pi      r p e   -> do
    -- Γ ⊢ A : Type
    p' <- checkParam p

    -- Γ, x : A ⊢ B : Type
    e' <- localParam p' $ checkExpr e Type

    -- ⟹ Γ ⊢ (Π x : A. B) : Type
    let t   = Pi (A.paramType p') (A.exprTerm e')
    i <- expect r t Type expectedTy
    return $ A.Pi i p' e'

  C.Lam     r p e   -> do
    -- Γ ⊢ A : Type
    p' <- checkParam p

    -- Γ, x : A ⊢ e : B
    tyB <- localParam p'  $ createMeta r Type
    e'  <- localParam p' $ checkExpr e tyB

    -- ⟹ Γ ⊢ (λ x : A. e) : (Π x : A. B)
    let t   = Lam (A.exprTerm e')
        ty  = Pi (A.paramType p') (A.exprType e')
    i <- expect r t ty expectedTy
    return $ A.Lam i p' e'

  C.Sigma   _ _ _   -> error "Σ-types"

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

  C.Times   _ _  _  -> error "Σ-types"

  C.Equals  r e1 e2 -> do
    -- Desugar a = b to Id (_ : Type) a b
    -- TODO: check type of Id is correct! 
    id  <- lookupState "Id" globalNames >>= \case
      Nothing -> error "missing builtin Id"
      Just id -> return id
    tyA <- createMeta r Type
    e1' <- checkExpr e1 tyA
    e2' <- checkExpr e2 tyA
    let t   = App (Axiom id) [tyA, A.exprTerm e1', A.exprTerm e2']
    i <- expect r t Type expectedTy
    return $ A.Equals i e1' e2'

  C.Pair    _ _  _  -> error "Σ-types"

-- | Given (x : A), check Γ ⊢ A : Type and construct a param for x.
checkParam :: C.Param -> M A.Param
checkParam (C.Param implicit n ann) = do
  n' <- createName n
  (ty', ann') <- case ann of
    Nothing -> do
      ty <- createMeta (A.nameRange n') Type
      return (ty, Nothing)
    Just ty -> do
      ty' <- checkExpr ty Type
      return (A.exprTerm ty', Just ty')
  return $ A.Param implicit n' ty' ann'

checkParams :: [C.Param] -> M [A.Param]
checkParams [] = return []
checkParams (p:ps) = do
  p' <- checkParam p
  ps' <- localParam p' $ checkParams ps
  return (p':ps')

termToPattern :: Term -> MaybeT M Pattern
termToPattern t = lift (whnf t) >>= \case
  App (Var i) []     -> return (VarPat i)
  App (Axiom i) args -> AxiomPat i <$> mapM termToPattern args
  _ -> mzero

checkDecl :: C.Decl -> M A.Decl
checkDecl = \case
  C.Define n params ann e -> do
    debug $ "checking definition" <+> pretty (C.nameText n) <+> "..."
    params' <- checkParams params
    (ctx, def, e') <- localParams params' $ do
      ctx <- asks envCtx
      def <- checkParam (C.Param Explicit n ann)
      e'  <- checkExpr e (A.paramType def)
      return (ctx, def, e')
    solveConstraints
    let n' = A.paramName def
        ty = ctxPi ctx (A.exprType e')
        tm = ctxLam ctx (A.exprTerm e')
    modify $ \s -> s
      { globalNames = HashMap.insert (A.nameText n') (A.nameId n') (globalNames s)
      , defNames    = HashMap.insert (A.nameId n') n' (defNames s)
      , defTypes    = HashMap.insert (A.nameId n') ty (defTypes s)
      , defTerms    = HashMap.insert (A.nameId n') tm (defTerms s)
      }
    return $ A.Define params' def e'
  C.Assume n params ann -> do
    debug $ "checking axiom" <+> pretty (C.nameText n) <+> "..."
    params' <- checkParams params
    (ctx, def) <- localParams params' $ do
      ctx <- asks envCtx
      def <- checkParam (C.Param Explicit n (Just ann))
      return (ctx, def)
    solveConstraints
    let n' = A.paramName def
        ty = ctxPi ctx (A.paramType def)
    modify $ \s -> s
      { globalNames = HashMap.insert (A.nameText n') (A.nameId n') (globalNames s)
      , axiomNames  = HashMap.insert (A.nameId n') n' (axiomNames s)
      , axiomTypes  = HashMap.insert (A.nameId n') ty (axiomTypes s)
      }
    return $ A.Assume params' def
  C.Rewrite n params lhs rhs -> do
    debug $ "checking rewrite" <+> pretty (C.nameText n) <+> "..."
    params' <- checkParams params
    (ctx, def, lhs', rhs') <- localParams params' $ do
      ctx  <- asks envCtx
      def  <- checkParam (C.Param Explicit n Nothing)
      lhs' <- checkExpr lhs (A.paramType def)
      rhs' <- checkExpr rhs (A.paramType def)
      return (ctx, def, lhs', rhs')
    solveConstraints
    runMaybeT (termToPattern (A.exprTerm lhs')) >>= \case
      Just (AxiomPat h args) -> do
        let rule = Rule
              { ruleCtxLength = ctxLength ctx
              , ruleHead      = h
              , ruleArgs      = args
              , ruleRhs       = ctxLam ctx (A.exprTerm rhs')
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

checkModule :: C.Module -> M A.Module
checkModule (C.Module decls) = A.Module <$> mapM checkDecl decls
