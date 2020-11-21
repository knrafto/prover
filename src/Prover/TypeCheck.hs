-- | Translates concrete syntax into abstract syntax, while generating
-- metavariables and type-checking constraints along the way. See Francesco
-- Mazzoli and Andreas Abel, "Type checking through unification",
-- https://arxiv.org/pdf/1609.09709v1.pdf.
module Prover.TypeCheck where

import Control.Monad
import Data.List

import Control.Monad.State.Class
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Text (Text)
import Prettyprinter

import Prover.InfixParser
import Prover.Monad
import Prover.Pattern
import Prover.Position
import Prover.Pretty
import Prover.Syntax.Abstract qualified as A
import Prover.Syntax.Concrete qualified as C
import Prover.Term
import Prover.Unify

-- A context with variable names.
data TcCtx
  = EmptyTcCtx
  | !TcCtx :>> (Maybe A.Name, Type)

-- | Strip the names from a type-checking context.
toCtx :: TcCtx -> Ctx
toCtx EmptyTcCtx = EmptyCtx
toCtx (tcCtx :>> (_, ty)) = toCtx tcCtx :> ty

-- | Look up a local variable name.
lookupLocal :: Text -> TcCtx -> Maybe (Var, A.Name)
lookupLocal t = go 0
  where
    go _ EmptyTcCtx = Nothing
    go !i (_ :>> (Just n, _))
      | A.nameText n == t = Just (i, n)
    go !i (tcCtx :>> _) = go (i + 1) tcCtx

-- | Add a param to the context.
addParam :: TcCtx -> A.Param -> TcCtx
addParam tcCtx p = tcCtx :>> (Just (A.paramName p), A.paramType p)

-- | Add a param group to the context.
addParamGroup :: TcCtx -> A.ParamGroup -> TcCtx
addParamGroup tcCtx (A.ParamGroup ps _) = foldl' addParam tcCtx ps

-- | Add param groups to the context.
addParams :: TcCtx -> [A.ParamGroup] -> TcCtx
addParams = foldl' addParamGroup

-- | Add an unnamed param to the environment.
addUnnamed :: TcCtx -> Type -> TcCtx
addUnnamed tcCtx ty = tcCtx :>> (Nothing, ty)

-- | Create a metavariable with the given type in the given context.
createMeta :: Range -> TcCtx -> Type -> M Term
createMeta r tcCtx ty = do
  let ctx = toCtx tcCtx
  id  <- freshMetaId
  -- Metavariables always represent closed terms, so in a context Γ we create
  -- a function Γ → A and apply it to all the variables in Γ.
  let metaTy = ctxPi ctx ty
  modify $ \s -> s
    { metaRanges  = HashMap.insert id r (metaRanges s)
    , unificationProblem = addProblemMeta id metaTy (unificationProblem s)
    }
  return $ Meta id (ctxVars ctx)

-- | Create a new name.
createName :: C.Name -> M A.Name
createName (C.Name r t) = do
  id <- freshNameId
  return (A.Name id r t)

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

-- | Check that there is a unique solution to the unification problem (and
-- report any errors if not).
checkSolved :: M ()
checkSolved = do
  problem <- gets unificationProblem
  -- Report unsolved constraints
  forM_ (HashMap.toList (problemConstraints problem)) $ \(id, _) -> do
    r <- getState id equationRanges
    -- TODO: show original equation
    emitError $ UnsolvedConstraint r
  -- Report unsolved metas
  forM_ (problemUnsolvedMetas problem) $ \id -> do
    r <- getState id metaRanges
    -- TODO: show type of meta
    emitError $ UnsolvedMeta r id
  -- Clear problem and merge into global substitution
  modify $ \s -> s
    { metaTypes = HashMap.union (problemMetaTypes problem) (metaTypes s)
    , metaTerms = HashMap.union (problemMetaTerms problem) (metaTerms s)
    , unificationProblem = emptyProblem
    }

-- | Generate expression info for a range, term, and type, while checking that
-- it matches the expected output type. Internally this generates a constraint
-- that two terms (of possibly different types) are equal, and simplify the
-- unification problem.
expect :: Range -> TcCtx -> Term -> Type -> Type -> M A.ExprInfo
expect r tcCtx b tyB tyA = do
  let ctx = toCtx tcCtx
  a <- createMeta r tcCtx tyA
  problem <- gets unificationProblem
  id <- freshEquationId
  let c = Guarded (TermEq ctx Type tyA tyB) (TermEq ctx tyA a b)
  problem' <- simplifyProblem (addProblemConstraint id c problem)
  modify $ \s -> s
    { equationRanges = HashMap.insert id r (equationRanges s)
    , unificationProblem = problem'
    }

  let subst = problemMetaTerms problem'
  debugFields ("checking expression at" <+> pretty r)
    [ "newly solved metas" |: do
      let solvedMetas =
            HashSet.difference
              (HashMap.keysSet (problemMetaTerms problem'))
              (HashMap.keysSet (problemMetaTerms problem))
      docs <- forM (HashSet.toList solvedMetas) $ \m -> do
        tmDoc <- prettyTerm subst EmptyCtx (problemMetaTerms problem' HashMap.! m)
        return $ prettyMeta m <+> "↦" <+> tmDoc
      return $ vsep docs
    , "unsolved metas" |: do
      let unsolvedMetas = HashSet.difference
              (HashMap.keysSet (problemMetaTypes problem'))
              (HashMap.keysSet (problemMetaTerms problem'))
      docs <- forM (HashSet.toList unsolvedMetas) $ \m -> do
        tyDoc <- prettyTerm subst EmptyCtx (problemMetaTypes problem' HashMap.! m)
        return $ prettyMeta m <+> ":" <+> tyDoc
      return $ vsep docs
    , "constraints" |: do
      docs <- mapM (prettyConstraint subst) (HashMap.elems (problemConstraints problem'))
      return $ vsep docs
    , "context" |: prettyCtx subst ctx
    , "type" |: prettyTerm subst ctx tyA
    , "term" |: prettyTerm subst ctx a
    ]

  return $ A.ExprInfo r a tyA

-- | Apply a term to metavariables to fill implicit parameters.
expandImplicits :: Range -> TcCtx -> Int -> Term -> Type -> M (Term, Type)
expandImplicits _ _     0 t ty = return (t, ty)
expandImplicits r tcCtx n t ty = do
  (a, b) <- case ty of
    Pi a b -> return (a, b)
    _ -> error "expandImplicits: not a Π-type"
  arg <- createMeta r tcCtx a
  expandImplicits r tcCtx (n - 1) (applyTerm t [arg]) (instantiate b arg)

-- | Producing a judgement Γ ⊢ t : A.
checkExpr :: C.Expr -> TcCtx -> Type -> M A.Expr
checkExpr expr tcCtx expectedTy = case expr of
  C.Id      n       -> do
    let r = C.nameRange n
        s = C.nameText n
    state <- get
    case () of
      _ | Just (v, n) <- lookupLocal s tcCtx -> do
          let t    = var v
              ty   = ctxLookup (toCtx tcCtx) v
              n'   = A.Name (A.nameId n) r s
          i <- expect r tcCtx t ty expectedTy
          return $ A.Var i n'

      _ | Just id <- HashMap.lookup s (globalNames state)
        , Just ty <- HashMap.lookup id (defTypes state) -> do
          implicits <- getState id defImplicits
          let n' = A.Name id r s
              t = Def id []
          (t', ty') <- expandImplicits r tcCtx implicits t ty
          i <- expect r tcCtx t' ty' expectedTy
          return $ A.Def i n'

      _ | Just id <- HashMap.lookup s (globalNames state)
        , Just ty <- HashMap.lookup id (axiomTypes state) -> do
          implicits <- getState id axiomImplicits
          let n' = A.Name id r s
              t  = Axiom id []
          (t', ty') <- expandImplicits r tcCtx implicits t ty
          i <- expect r tcCtx t' ty' expectedTy
          return $ A.Axiom i n'

      _ -> do
        emitError $ UnboundName r s
        t <- createMeta r tcCtx expectedTy
        return $ A.Unbound (A.ExprInfo r t expectedTy) s

  C.Hole    r       -> do
    t <- createMeta r tcCtx expectedTy
    return $ A.Hole (A.ExprInfo r t expectedTy)

  C.Type    r       -> do
    i <- expect r tcCtx Type Type expectedTy
    return $ A.Type i

  C.Pi      r ps e  -> do
    -- Γ ⊢ A : Type
    ps' <- checkParams tcCtx ps

    -- Γ, x : A ⊢ B : Type
    e' <- checkExpr e (addParams tcCtx ps') Type

    -- ⟹ Γ ⊢ (Π x : A. B) : Type
    let t = paramsPi ps' (A.exprTerm e')
    i <- expect r tcCtx t Type expectedTy
    return $ A.Pi i ps' e'

  C.Lam     r ps e  -> do
    -- Γ ⊢ A : Type
    ps' <- checkParams tcCtx ps

    -- Γ, x : A ⊢ e : B
    tyB <- createMeta r (addParams tcCtx ps') Type
    e'  <- checkExpr e (addParams tcCtx ps') tyB

    -- ⟹ Γ ⊢ (λ x : A. e) : (Π x : A. B)
    let t   = paramsLam ps' (A.exprTerm e')
        ty  = paramsPi ps' (A.exprType e')
    i <- expect r tcCtx t ty expectedTy
    return $ A.Lam i ps' e'

  C.Sigma   r ps e  -> do
    -- Γ ⊢ A : Type
    ps' <- checkParams tcCtx ps

    -- Γ, x : A ⊢ B : Type
    e' <- checkExpr e (addParams tcCtx ps') Type

    -- ⟹ Γ ⊢ (Σ x : A. B) : Type
    let t = paramsSigma ps' (A.exprTerm e')
    i <- expect r tcCtx t Type expectedTy
    return $ A.Sigma i ps' e'

  C.Apps    r es    -> do
    tree <- parseInfixOperators r es
    checkInfixTree tree tcCtx expectedTy

  C.Arrow   r e1 e2 -> do
    -- Γ ⊢ A : Type
    e1' <- checkExpr e1 tcCtx Type

    -- Γ ⊢ B : Type
    e2' <- checkExpr e2 tcCtx Type

    -- ⟹ Γ ⊢ (Π _ : A. B) : Type
    let t = Pi (A.exprTerm e1') (weaken (A.exprTerm e2'))
    i <- expect r tcCtx t Type expectedTy
    return $ A.Arrow i e1' e2'

  C.Pair    r a  b  -> do
    -- Γ ⊢ a : A
    tyA <- createMeta r tcCtx Type
    a' <- checkExpr a tcCtx tyA

    -- Γ ⊢ b : B a
    tyB <- createMeta r (addUnnamed tcCtx tyA) Type
    b' <- checkExpr b tcCtx (instantiate tyB (A.exprTerm a'))

    -- ⟹ Γ ⊢ (a, b) : Σ _ : A. B
    let t  = Pair (A.exprTerm a') (A.exprTerm b')
        ty = Sigma tyA tyB
    i <- expect r tcCtx t ty expectedTy
    return $ A.Pair i a' b'

checkInfixTree :: InfixTree -> TcCtx -> Type -> M A.Expr
checkInfixTree tree tcCtx expectedTy = case tree of
  Atom e    -> checkExpr e tcCtx expectedTy
  App r f a -> do
    -- Γ ⊢ a : A
    tyA <- createMeta r tcCtx Type
    a'  <- checkInfixTree a tcCtx tyA

    -- Γ ⊢ f : (Π x : A. B)
    tyB <- createMeta r (addUnnamed tcCtx tyA) Type
    f'  <- checkInfixTree f tcCtx (Pi tyA tyB)

    -- ⟹ Γ ⊢ f a : B[a/x]
    -- TODO: a chained application is currently quadratic in the number of
    -- arguments
    let t  = applyTerm (A.exprTerm f') [A.exprTerm a']
        ty = instantiate tyB (A.exprTerm a') 
    i <- expect r tcCtx t ty expectedTy
    return $ A.App i f' a'

-- | Given (x : A), check Γ ⊢ A : Type and construct a param for x.
checkParamNames :: TcCtx -> [C.Name] -> Type -> M [A.Param]
checkParamNames _ [] _ = return []
checkParamNames tcCtx (n:ns) ty = do
  n' <- createName n
  let p = A.Param n' ty
  ps <- checkParamNames (addParam tcCtx p) ns (weaken ty)
  return (p:ps)

-- | Given (x : A), check Γ ⊢ A : Type and construct a param for x.
checkParamGroup :: TcCtx -> C.ParamGroup -> M A.ParamGroup
checkParamGroup tcCtx (C.ParamGroup ns ann) = do
  (ty', ann') <- case ann of
    Nothing -> do
      -- TODO: is this the right range? or should it be all of them?
      ty <- createMeta (C.nameRange (head ns)) tcCtx Type
      return (ty, Nothing)
    Just ty -> do
      ty' <- checkExpr ty tcCtx Type
      return (A.exprTerm ty', Just ty')
  ps <- checkParamNames tcCtx ns ty'
  return $ A.ParamGroup ps ann'

checkParams :: TcCtx -> [C.ParamGroup] -> M [A.ParamGroup]
checkParams _ [] = return []
checkParams tcCtx (p:ps) = do
  p' <- checkParamGroup tcCtx p
  ps' <- checkParams (addParamGroup tcCtx p') ps
  return (p':ps')

termToPattern :: Term -> MaybeT M Pattern
termToPattern = \case
  Meta id args -> lift (lookupState id metaTerms) >>= \case
    Just t' -> termToPattern (applyTerm t' args)
    Nothing -> mzero
  Var i []     -> return (VarPat i)
  Axiom i args -> AxiomPat i <$> mapM termToPattern args
  Pair a b     -> PairPat <$> termToPattern a <*> termToPattern b
  _            -> mzero

checkDecl :: C.Decl -> M A.Decl
checkDecl = \case
  C.Define n implicits explicits ann e -> do
    debug $ "checking definition" <+> pretty (C.nameText n) <+> "..."
    params' <- checkParams EmptyTcCtx (implicits ++ explicits)
    n' <- createName n
    let tcCtx = addParams EmptyTcCtx params'
    (ty, ann') <- case ann of
      Nothing -> do
        ty <- createMeta (A.nameRange n') tcCtx Type
        return (ty, Nothing)
      Just ann -> do
        ann' <- checkExpr ann tcCtx Type
        return (A.exprTerm ann', Just ann')
    e' <- checkExpr e tcCtx ty
    checkSolved
    let def' = A.Param n' ty
    modify $ \s -> s
      { globalNames  = HashMap.insert (A.nameText n') (A.nameId n') (globalNames s)
      , defNames     = HashMap.insert (A.nameId n') n' (defNames s)
      , defImplicits = HashMap.insert (A.nameId n') (length implicits) (defImplicits s)
      , defTypes     = HashMap.insert (A.nameId n') (paramsPi params' (A.exprType e')) (defTypes s)
      , defTerms     = HashMap.insert (A.nameId n') (paramsLam params' (A.exprTerm e')) (defTerms s)
      }
    return $ A.Define params' def' ann' e'
  C.Assume n implicits explicits ann -> do
    debug $ "checking axiom" <+> pretty (C.nameText n) <+> "..."
    params' <- checkParams EmptyTcCtx (implicits ++ explicits)
    n' <- createName n
    let tcCtx = addParams EmptyTcCtx params'
    ann' <- checkExpr ann tcCtx Type
    checkSolved
    let def' = A.Param n' (A.exprTerm ann')
    modify $ \s -> s
      { globalNames    = HashMap.insert (A.nameText n') (A.nameId n') (globalNames s)
      , axiomNames     = HashMap.insert (A.nameId n') n' (axiomNames s)
      , axiomImplicits = HashMap.insert (A.nameId n') (length implicits) (axiomImplicits s)
      , axiomTypes     = HashMap.insert (A.nameId n') (paramsPi params' (A.exprTerm ann')) (axiomTypes s)
      }
    return $ A.Assume params' def' ann'
  C.Rewrite n params lhs rhs -> do
    debug $ "checking rewrite" <+> pretty (C.nameText n) <+> "..."
    params' <- checkParams EmptyTcCtx params
    n' <- createName n
    let tcCtx = addParams EmptyTcCtx params'
    ty <- createMeta (A.nameRange n') tcCtx Type
    lhs' <- checkExpr lhs tcCtx ty
    rhs' <- checkExpr rhs tcCtx ty
    let def' = A.Param n' ty
    checkSolved
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
    return $ A.Rewrite params' def' lhs' rhs'
  C.Fixity fixity prec n -> do
    modify $ \s -> s { fixities = HashMap.insert n (fixity, prec) (fixities s) }
    return $ A.Fixity fixity prec n

checkModule :: C.Module -> M A.Module
checkModule (C.Module decls) = A.Module <$> mapM checkDecl decls
