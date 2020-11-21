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
import Prover.Syntax
import Prover.Syntax.Concrete qualified as C
import Prover.Term
import Prover.Unify

-- A context with variable names.
data TcCtx
  = EmptyTcCtx
  | !TcCtx :>> (Maybe Name, Type)

-- | Strip the names from a type-checking context.
toCtx :: TcCtx -> Ctx
toCtx EmptyTcCtx = EmptyCtx
toCtx (tcCtx :>> (_, ty)) = toCtx tcCtx :> ty

-- | Look up a local variable name.
lookupLocal :: Text -> TcCtx -> Maybe (Var, Name)
lookupLocal t = go 0
  where
    go _ EmptyTcCtx = Nothing
    go !i (_ :>> (Just n, _))
      | nameText n == t = Just (i, n)
    go !i (tcCtx :>> _) = go (i + 1) tcCtx

-- | Add a param to the context.
addParam :: TcCtx -> Name -> TcCtx
addParam tcCtx n = tcCtx :>> (Just n, nameType n)

-- | Add a param group to the context.
addParamGroup :: TcCtx -> ParamGroup ExprInfo Name -> TcCtx
addParamGroup tcCtx (ParamGroup ns _) = foldl' addParam tcCtx ns

-- | Add param groups to the context.
addParamGroups :: TcCtx -> [ParamGroup ExprInfo Name] -> TcCtx
addParamGroups = foldl' addParamGroup

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

-- | The number of variables in the parameter collection.
paramsLength :: [ParamGroup ExprInfo Name] -> Int
paramsLength = sum . map (\(ParamGroup ns _) -> length ns)

-- | Desugar parameters into a bunch of Π binders.
paramsPi :: [ParamGroup ExprInfo Name] -> Type -> Type
paramsPi [] ty = ty
paramsPi (ParamGroup ns _ : rest) ty = paramListPi ns $ paramsPi rest ty
  where
    paramListPi :: [Name] -> Type -> Type
    paramListPi [] ty  = ty
    paramListPi (n:ns) ty = Pi (nameType n) (paramListPi ns ty)

-- | Desugar parameters into a bunch of Σ binders.
paramsSigma :: [ParamGroup ExprInfo Name] -> Type -> Type
paramsSigma [] ty = ty
paramsSigma (ParamGroup ns _ : rest) ty = paramListSigma ns $ paramsSigma rest ty
  where
    paramListSigma :: [Name] -> Type -> Type
    paramListSigma [] ty  = ty
    paramListSigma (n:ns) ty = Sigma (nameType n) (paramListSigma ns ty)

-- | Desugar parameters into a bunch of λ binders.
paramsLam :: [ParamGroup ExprInfo Name] -> Term -> Term
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
expect :: Range -> TcCtx -> Term -> Type -> Type -> M ExprInfo
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

  return $ ExprInfo r a tyA

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
checkExpr :: C.Expr -> TcCtx -> Type -> M (Expr ExprInfo Name)
checkExpr expr tcCtx expectedTy = case expr of
  C.Id      n       -> do
    let r = C.nameRange n
        s = C.nameText n
    state <- get
    case () of
      _ | Just (v, n) <- lookupLocal s tcCtx -> do
          let t    = var v
              ty   = ctxLookup (toCtx tcCtx) v
          i <- expect r tcCtx t ty expectedTy
          return $ EVar i n

      _ | Just id <- HashMap.lookup s (globalNames state)
        , Just ty <- HashMap.lookup id (defTypes state) -> do
          implicits <- getState id defImplicits
          let n' = Name r s (DefName id) ty
              t = Def id []
          (t', ty') <- expandImplicits r tcCtx implicits t ty
          i <- expect r tcCtx t' ty' expectedTy
          return $ EVar i n'

      _ | Just id <- HashMap.lookup s (globalNames state)
        , Just ty <- HashMap.lookup id (axiomTypes state) -> do
          implicits <- getState id axiomImplicits
          let n' = Name r s (AxiomName id) ty
              t  = Axiom id []
          (t', ty') <- expandImplicits r tcCtx implicits t ty
          i <- expect r tcCtx t' ty' expectedTy
          return $ EVar i n'

      _ -> do
        emitError $ UnboundNameError r s
        t <- createMeta r tcCtx expectedTy
        let n' = Name r s UnboundName expectedTy
        return $ EVar (ExprInfo r t expectedTy) n'

  C.Hole    r       -> do
    t <- createMeta r tcCtx expectedTy
    return $ EHole (ExprInfo r t expectedTy)

  C.Type    r       -> do
    i <- expect r tcCtx Type Type expectedTy
    return $ EType i

  C.Pi      r ps e  -> do
    -- Γ ⊢ A : Type
    ps' <- checkParamGroups tcCtx ps

    -- Γ, x : A ⊢ B : Type
    e' <- checkExpr e (addParamGroups tcCtx ps') Type

    -- ⟹ Γ ⊢ (Π x : A. B) : Type
    let t = paramsPi ps' (exprTerm e')
    i <- expect r tcCtx t Type expectedTy
    return $ EPi i ps' e'

  C.Lam     r ps e  -> do
    -- Γ ⊢ A : Type
    ps' <- checkParamGroups tcCtx ps

    -- Γ, x : A ⊢ e : B
    tyB <- createMeta r (addParamGroups tcCtx ps') Type
    e'  <- checkExpr e (addParamGroups tcCtx ps') tyB

    -- ⟹ Γ ⊢ (λ x : A. e) : (Π x : A. B)
    let t   = paramsLam ps' (exprTerm e')
        ty  = paramsPi ps' (exprType e')
    i <- expect r tcCtx t ty expectedTy
    return $ ELam i ps' e'

  C.Sigma   r ps e  -> do
    -- Γ ⊢ A : Type
    ps' <- checkParamGroups tcCtx ps

    -- Γ, x : A ⊢ B : Type
    e' <- checkExpr e (addParamGroups tcCtx ps') Type

    -- ⟹ Γ ⊢ (Σ x : A. B) : Type
    let t = paramsSigma ps' (exprTerm e')
    i <- expect r tcCtx t Type expectedTy
    return $ ESigma i ps' e'

  C.Apps    r es    -> do
    tree <- parseInfixOperators r es
    checkInfixTree tree tcCtx expectedTy

  C.Arrow   r e1 e2 -> do
    -- Γ ⊢ A : Type
    e1' <- checkExpr e1 tcCtx Type

    -- Γ ⊢ B : Type
    e2' <- checkExpr e2 tcCtx Type

    -- ⟹ Γ ⊢ (Π _ : A. B) : Type
    let t = Pi (exprTerm e1') (weaken (exprTerm e2'))
    i <- expect r tcCtx t Type expectedTy
    return $ EArrow i e1' e2'

  C.Pair    r a  b  -> do
    -- Γ ⊢ a : A
    tyA <- createMeta r tcCtx Type
    a' <- checkExpr a tcCtx tyA

    -- Γ ⊢ b : B a
    tyB <- createMeta r (addUnnamed tcCtx tyA) Type
    b' <- checkExpr b tcCtx (instantiate tyB (exprTerm a'))

    -- ⟹ Γ ⊢ (a, b) : Σ _ : A. B
    let t  = Pair (exprTerm a') (exprTerm b')
        ty = Sigma tyA tyB
    i <- expect r tcCtx t ty expectedTy
    return $ EPair i a' b'

checkInfixTree :: InfixTree -> TcCtx -> Type -> M (Expr ExprInfo Name)
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
    let t  = applyTerm (exprTerm f') [exprTerm a']
        ty = instantiate tyB (exprTerm a') 
    i <- expect r tcCtx t ty expectedTy
    return $ EApp i f' a'

-- | Create a new name.
checkParam :: C.Name -> Type -> M Name
checkParam (C.Name r t) ty = do
  id <- freshNameId
  return $ Name r t (LocalName id) ty

-- | Given (x : A), check Γ ⊢ A : Type and construct a param for x.
checkParams :: TcCtx -> [C.Name] -> Type -> M [Name]
checkParams _ [] _ = return []
checkParams tcCtx (n:ns) ty = do
  n' <- checkParam n ty
  ns' <- checkParams (addParam tcCtx n') ns (weaken ty)
  return (n':ns')

-- | Given (x : A), check Γ ⊢ A : Type and construct a param for x.
checkParamGroup :: TcCtx -> C.ParamGroup -> M (ParamGroup ExprInfo Name)
checkParamGroup tcCtx (C.ParamGroup ns ann) = do
  (ty', ann') <- case ann of
    Nothing -> do
      -- TODO: is this the right range? or should it be all of them?
      ty <- createMeta (C.nameRange (head ns)) tcCtx Type
      return (ty, Nothing)
    Just ty -> do
      ty' <- checkExpr ty tcCtx Type
      return (exprTerm ty', Just ty')
  ns' <- checkParams tcCtx ns ty'
  return $ ParamGroup ns' ann'

checkParamGroups :: TcCtx -> [C.ParamGroup] -> M [ParamGroup ExprInfo Name]
checkParamGroups _ [] = return []
checkParamGroups tcCtx (n:ns) = do
  n' <- checkParamGroup tcCtx n
  ns' <- checkParamGroups (addParamGroup tcCtx n') ns
  return (n':ns')

termToPattern :: Term -> MaybeT M Pattern
termToPattern = \case
  Meta id args -> lift (lookupState id metaTerms) >>= \case
    Just t' -> termToPattern (applyTerm t' args)
    Nothing -> mzero
  Var i []     -> return (VarPat i)
  Axiom i args -> AxiomPat i <$> mapM termToPattern args
  Pair a b     -> PairPat <$> termToPattern a <*> termToPattern b
  _            -> mzero

checkDecl :: C.Decl -> M (Decl ExprInfo Name)
checkDecl = \case
  C.Define n implicits explicits ann e -> do
    debug $ "checking definition" <+> pretty (C.nameText n) <+> "..."
    implicits' <- checkParamGroups EmptyTcCtx implicits
    explicits' <- checkParamGroups (addParamGroups EmptyTcCtx implicits') explicits
    id <- freshNameId
    let params' = implicits' ++ explicits'
    let tcCtx = addParamGroups EmptyTcCtx params'
    (ty, ann') <- case ann of
      Nothing -> do
        ty <- createMeta (C.nameRange n) tcCtx Type
        return (ty, Nothing)
      Just ann -> do
        ann' <- checkExpr ann tcCtx Type
        return (exprTerm ann', Just ann')
    e' <- checkExpr e tcCtx ty
    checkSolved
    let n' = Name (C.nameRange n) (C.nameText n) (DefName id) ty
    modify $ \s -> s
      { globalNames  = HashMap.insert (nameText n') id (globalNames s)
      , defNames     = HashMap.insert id n' (defNames s)
      , defImplicits = HashMap.insert id (length implicits) (defImplicits s)
      , defTypes     = HashMap.insert id (paramsPi params' (exprType e')) (defTypes s)
      , defTerms     = HashMap.insert id (paramsLam params' (exprTerm e')) (defTerms s)
      }
    return $ Define n' implicits' explicits' ann' e'
  C.Assume n implicits explicits ann -> do
    debug $ "checking axiom" <+> pretty (C.nameText n) <+> "..."
    implicits' <- checkParamGroups EmptyTcCtx implicits
    explicits' <- checkParamGroups (addParamGroups EmptyTcCtx implicits') explicits
    id <- freshNameId
    let params' = implicits' ++ explicits'
    let tcCtx = addParamGroups EmptyTcCtx params'
    ann' <- checkExpr ann tcCtx Type
    checkSolved
    let n' = Name (C.nameRange n) (C.nameText n) (AxiomName id) (exprTerm ann')
    modify $ \s -> s
      { globalNames    = HashMap.insert (nameText n') id (globalNames s)
      , axiomNames     = HashMap.insert id n' (axiomNames s)
      , axiomImplicits = HashMap.insert id (length implicits) (axiomImplicits s)
      , axiomTypes     = HashMap.insert id (paramsPi params' (exprTerm ann')) (axiomTypes s)
      }
    return $ Assume n' implicits' explicits' ann'
  C.Rewrite n params lhs rhs -> do
    debug $ "checking rewrite" <+> pretty (C.nameText n) <+> "..."
    params' <- checkParamGroups EmptyTcCtx params
    let tcCtx = addParamGroups EmptyTcCtx params'
    ty <- createMeta (C.nameRange n) tcCtx Type
    lhs' <- checkExpr lhs tcCtx ty
    rhs' <- checkExpr rhs tcCtx ty
    checkSolved
    let n' = Name (C.nameRange n) (C.nameText n) RewriteName ty
    runMaybeT (termToPattern (exprTerm lhs')) >>= \case
      Just (AxiomPat h args) -> do
        let rule = Rule
              { ruleCtxLength = paramsLength params'
              , ruleHead      = h
              , ruleArgs      = args
              , ruleRhs       = paramsLam params' (exprTerm rhs')
              }
        if matchable rule then
          -- TODO: validate is matchable
          modify $ \s -> s
            { axiomRules = HashMap.insertWith (++) (ruleHead rule) [rule] (axiomRules s)
            }
        else
          emitError $ MissingPatternVariable (exprRange lhs')
      _ -> emitError $ BadPattern (exprRange lhs')
    return $ Rewrite n' params' lhs' rhs'
  C.Fixity fixity prec n -> do
    modify $ \s -> s { fixities = HashMap.insert n (fixity, prec) (fixities s) }
    return $ Fixity fixity prec n

checkModule :: C.Module -> M (Module ExprInfo Name)
checkModule (C.Module decls) = Module <$> mapM checkDecl decls
