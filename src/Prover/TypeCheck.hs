-- | Translates concrete syntax into abstract syntax, while generating
-- metavariables and type-checking constraints along the way. See Francesco
-- Mazzoli and Andreas Abel, "Type checking through unification",
-- https://arxiv.org/pdf/1609.09709v1.pdf.
module Prover.TypeCheck where

import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import Prettyprinter

import Prover.Monad
import Prover.Pretty
import qualified Prover.Syntax.Abstract as A
import qualified Prover.Syntax.Concrete as C
import Prover.Syntax.Internal
import Prover.Syntax.Position

-- | Create a metavariable with the given type in the given context.
createMeta :: Range -> Type -> M Term
createMeta r ty = do
  ctx <- asks envCtx
  id  <- freshMetaId
  -- Metavariables always represent closed terms, so in a context Γ we create
  -- a function Γ → A and apply it to all the variables in Γ.
  let metaTy = ctxPi ctx ty
  modify $ \s -> s { metaTypes = HashMap.insert id metaTy (metaTypes s) }
  debugFields "created meta" $
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

-- | Type-check with a new binding.
extendEnv :: Maybe A.Name -> Type -> M a -> M a
extendEnv n ty = local $ \e -> Env
  { envVarNames = n : envVarNames e
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
  debugFields "created constraint" $
    [ "loc" |: return (pretty r)
    , "ctx" |: prettyCtx ctx
    , "a"   |: prettyTerm ctx a
    , "A"   |: prettyTerm ctx tyA
    , "b"   |: prettyTerm ctx b
    , "B"   |: prettyTerm ctx tyB
    ]

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

      _ -> throwError $ UnboundName r s

  C.Hole    r       -> do
    t <- createMeta r expectedTy
    return $ A.Hole (A.ExprInfo r t expectedTy)

  C.Type    r       -> do
    i <- expect r Type Type expectedTy
    return $ A.Type i

  C.Pi      r p e   -> do
    -- Γ ⊢ A : Type
    b@(A.Binding n tyA _) <- checkBinding p

    -- Γ, x : A ⊢ B : Type
    e' <- extendEnv (Just n) tyA $ checkExpr e Type

    -- ⟹ Γ ⊢ (Π x : A. B) : Type
    let t   = Pi tyA (A.exprTerm e')
    i <- expect r t Type expectedTy
    return $ A.Pi i b e'

  C.Lam     r p e   -> do
    -- Γ ⊢ A : Type
    b@(A.Binding n tyA _) <- checkBinding p

    -- Γ, x : A ⊢ e : B
    tyB <- extendEnv (Just n) tyA $ createMeta r Type
    e'  <- extendEnv (Just n) tyA $ checkExpr e tyB

    -- ⟹ Γ ⊢ (λ x : A. e) : (Π x : A. B)
    let t   = Lam (A.exprTerm e')
        ty  = Pi tyA (A.exprType e')
    i <- expect r t ty expectedTy
    return $ A.Lam i b e'

  C.Sigma   r _ _   -> throwError $ Unimplemented r "Σ-types"

  C.App     r f a   -> do
    -- Γ ⊢ a : A
    tyA <- createMeta r Type
    a'  <- checkExpr a tyA

    -- Γ ⊢ f : (Π x : A. B)
    tyB <- extendEnv Nothing tyA (createMeta r Type)
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
    let t = Pi (A.exprTerm e1') (weaken (A.exprTerm e1'))
    i <- expect r t Type expectedTy
    return $ A.Arrow i e1' e2'

  C.Times   r _  _  -> throwError $ Unimplemented r "Σ-types"

  C.Equals  r e1 e2 -> do
    -- Desugar a = b to Id (_ : Type) a b
    -- TODO: check type of Id is correct! 
    s   <- get
    id  <- case HashMap.lookup "Id" (globalNames s) of
      Nothing -> throwError $ MissingBuiltin r "Id"
      Just id -> return id
    tyA <- createMeta r Type
    e1' <- checkExpr e1 tyA
    e2' <- checkExpr e2 tyA
    let t   = App (Axiom id) [tyA, A.exprTerm e1', A.exprTerm e2']
    i <- expect r t Type expectedTy
    return $ A.Equals i e1' e2'

  C.Pair    r _  _  -> throwError $ Unimplemented r "Σ-types"

-- | Given (x : A), check Γ ⊢ A : Type and construct a binding for x.
checkBinding :: C.Param -> M A.Binding
checkBinding (n, ann) = do
  n' <- createName n
  (ty', ann') <- case ann of
    Nothing -> do
      ty <- createMeta (A.nameRange n') Type
      return (ty, Nothing)
    Just ty -> do
      ty' <- checkExpr ty Type
      return (A.exprTerm ty', Just ty')
  return $ A.Binding n' ty' ann'

checkDecl :: C.Decl -> M A.Decl
checkDecl = \case
  C.Define n ann e -> do
    debug $ "checking definition" <+> pretty (C.nameText n) <+> "..."
    b  <- checkBinding (n, ann)
    e' <- checkExpr e (A.bindingType b)
    let n' = A.bindingName b
    modify $ \s -> s
      { globalNames = HashMap.insert (A.nameText n') (A.nameId n') (globalNames s)
      , defNames    = HashMap.insert (A.nameId n') n' (defNames s)
      , defTypes    = HashMap.insert (A.nameId n') (A.exprType e') (defTypes s)
      , defTerms    = HashMap.insert (A.nameId n') (A.exprTerm e') (defTerms s)
      }
    return $ A.Define b e'
  C.Assume n ty   -> do
    debug $ "checking assumption" <+> pretty (C.nameText n) <+> "..."
    n'  <- createName n
    ty' <- checkExpr ty Type
    modify $ \s -> s
      { globalNames = HashMap.insert (A.nameText n') (A.nameId n') (globalNames s)
      , axiomNames  = HashMap.insert (A.nameId n') n' (axiomNames s)
      , axiomTypes  = HashMap.insert (A.nameId n') (A.exprTerm ty') (axiomTypes s)
      }
    return $ A.Assume (A.Binding n' (A.exprTerm ty') (Just ty'))

-- TODO: solve constraints after each decl
checkModule :: C.Module -> M A.Module
checkModule (C.Module decls) = A.Module <$> mapM checkDecl decls
