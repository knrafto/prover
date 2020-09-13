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
createMeta :: Type -> M Term
createMeta ty = do
  ctx <- asks envCtx
  id  <- freshMetaId
  -- Metavariables always represent closed terms, so in a context Γ we create
  -- a function Γ → A and apply it to all the variables in Γ.
  let metaTy = ctxPi ctx ty
  modify $ \s -> s { metaTypes = HashMap.insert id metaTy (metaTypes s) }
  debugFields "created meta" $
    [ "meta" |: return (prettyMeta id)
    , "ctx"  |: prettyCtx ctx
    , "type" |: prettyTerm ctx ty
    ]
  -- TODO: print debug info
  return $ App (Meta id) (ctxVars ctx)

-- | Create a new name.
createName :: C.Name -> M A.Name
createName (C.Name r t) = do
  id <- freshNameId
  return (A.Name id r t)

-- | Generate a constraint that two terms (of possibly different types) are
-- equal.
checkEqualTerms :: Range -> Term -> Type -> Term -> Type -> M ()
checkEqualTerms _ a tyA b tyB = do
  ctx <- asks envCtx
  debugFields "unify terms" $
    [ "ctx" |: prettyCtx ctx
    , "a"   |: prettyTerm ctx a
    , "A"   |: prettyTerm ctx tyA
    , "b"   |: prettyTerm ctx b
    , "B"   |: prettyTerm ctx tyB
    ]

-- | Generate a constraint that two types equal.
checkEqualTypes :: Range -> Type -> Type -> M ()
checkEqualTypes _ tyA tyB = do
  ctx <- asks envCtx
  debugFields "unify types" $
    [ "ctx" |: prettyCtx ctx
    , "A"   |: prettyTerm ctx tyA
    , "B"   |: prettyTerm ctx tyB
    ]

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

-- | Producing a judgement Γ ⊢ t : A.
checkExpr :: C.Expr -> M A.Expr
checkExpr = \case
  C.Id      n       -> do
    let r = C.nameRange n
        t = C.nameText n
    e <- ask
    s <- get
    case () of
      _ | Just (v, n) <- lookupLocal t (envVarNames e) -> do
          let ty   = ctxLookup (envCtx e) v
              info = A.ExprInfo r (App (Var v) []) ty
              n'   = A.Name (A.nameId n) r t
          return $ A.Var info n'

      _ | Just id <- HashMap.lookup t (globalNames s)
        , Just ty <- HashMap.lookup id (defTypes s) -> do
          let info = A.ExprInfo r (App (Def id) []) ty
              n'   = A.Name id r t
          return $ A.Def info n'

      _ | Just id <- HashMap.lookup t (globalNames s)
        , Just ty <- HashMap.lookup id (axiomTypes s) -> do
          let info = A.ExprInfo r (App (Axiom id) []) ty
              n'   = A.Name id r t
          return $ A.Axiom info n'

      _ -> throwError $ UnboundName r t

  C.Hole    r       -> do
    ty <- createMeta Type
    t  <- createMeta ty
    return $ A.Hole (A.ExprInfo r t ty)

  C.Type    r       -> do
    return $ A.Type (A.ExprInfo r Type Type)

  C.Pi      r p e   -> do
    -- Γ ⊢ A : Type
    b@(A.Binding n tyA _) <- checkBinding p

    -- Γ, x : A ⊢ B : Type
    e' <- extendEnv (Just n) tyA $ checkExprIsType e

    -- ⟹ Γ ⊢ (Π x : A. B) : Type
    let t   = Pi tyA (A.exprTerm e')
    return $ A.Pi (A.ExprInfo r t Type) b e'

  C.Lam     r p e   -> do
    -- Γ ⊢ A : Type
    b@(A.Binding n tyA _) <- checkBinding p

    -- Γ, x : A ⊢ e : B
    e' <- extendEnv (Just n) tyA $ checkExpr e

    -- ⟹ Γ ⊢ (λ x : A. e) : (Π x : A. B)
    let t   = Lam (A.exprTerm e')
        ty  = Pi tyA (A.exprType e')
    return $ A.Lam (A.ExprInfo r t ty) b e'

  C.Sigma   r _ _   -> throwError $ Unimplemented r "Σ-types"

  C.App     r f a   -> do
    -- Γ ⊢ a : A
    a' <- checkExpr a

    -- Γ ⊢ f : (Π x : A. B)
    let tyA = A.exprType a'
    tyB <- extendEnv Nothing tyA (createMeta Type)
    f'  <- checkExpr f
    checkEqualTypes r (A.exprType f') (Pi tyA tyB)

    -- ⟹ Γ ⊢ f a : B[a/x]
    checkApply f'
    -- TODO: a chained application is currently quadratic in the number of
    -- arguments
    let t  = applyTerm (A.exprTerm f') [A.exprTerm a']
        ty = instantiate tyB (A.exprTerm a') 
    return $ A.App (A.ExprInfo r t ty) f' a'
  C.Arrow   r e1 e2 ->  do
    -- Γ ⊢ A : Type
    e1' <- checkExprIsType e1

    -- Γ ⊢ B : Type
    e2' <- checkExprIsType e2

    -- ⟹ Γ ⊢ (Π _ : A. B) : Type
    let t   = Pi (A.exprTerm e1') (weaken (A.exprTerm e1'))
    return $ A.Arrow (A.ExprInfo r t Type) e1' e2'

  C.Times   r _  _  -> throwError $ Unimplemented r "Σ-types"

  C.Equals  r e1 e2 -> do
    -- Desugar a = b to Id (_ : Type) a b
    -- TODO: check type of Id is correct! 
    s   <- get
    id  <- case HashMap.lookup "Id" (globalNames s) of
      Nothing -> throwError $ MissingBuiltin r "Id"
      Just id -> return id
    a   <- createMeta Type
    e1' <- checkExpr e1
    e2' <- checkExpr e2
    let t   = App (Axiom id) [a, A.exprTerm e1', A.exprTerm e2']
    return $ A.Equals (A.ExprInfo r t Type) e1' e2'

  C.Pair    r _  _  -> throwError $ Unimplemented r "Σ-types"

-- | Produce a judgement Γ ⊢ t : Type.
checkExprIsType :: C.Expr -> M A.Expr
checkExprIsType e = do
  e' <- checkExpr e
  checkEqualTypes (getRange e') (A.exprType e') Type
  return e'

-- | Check that an expression can be applied to an argument before constructing
-- a term for the application (which would otherwise fail).
-- TODO: should we save the range of the larger application too?
checkApply :: A.Expr -> M ()
checkApply = \case
  A.Var     _ _   -> return ()
  A.Def     _ _   -> return ()
  A.Axiom   _ _   -> return ()
  A.Hole    _     -> return ()
  A.Lam     _ _ _ -> return ()
  A.App     _ _ _ -> return ()
  e               -> throwError $ CannotApply e

-- | Given (x : A), check Γ ⊢ A : Type and construct a binding for x.
checkBinding :: C.Param -> M A.Binding
checkBinding (n, ann) = do
  n' <- createName n
  (ty, ann') <- case ann of
    Nothing -> do
      ty <- createMeta Type
      return (ty, Nothing)
    Just e -> do
      e' <- checkExprIsType e
      return (A.exprTerm e', Just e')
  return $ A.Binding n' ty ann'

checkDecl :: C.Decl -> M A.Decl
checkDecl = \case
  C.Define n ann e -> do
    debug $ "checking definition" <+> pretty (C.nameText n) <+> "..."
    b  <- checkBinding (n, ann)
    e' <- checkExpr e
    checkEqualTypes (getRange e') (A.bindingType b) (A.exprType e')
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
    ty' <- checkExprIsType ty
    modify $ \s -> s
      { globalNames = HashMap.insert (A.nameText n') (A.nameId n') (globalNames s)
      , axiomNames  = HashMap.insert (A.nameId n') n' (axiomNames s)
      , axiomTypes  = HashMap.insert (A.nameId n') (A.exprTerm ty') (axiomTypes s)
      }
    return $ A.Assume (A.Binding n' (A.exprTerm ty') (Just ty'))

-- TODO: solve constraints after each decl
checkModule :: C.Module -> M A.Module
checkModule (C.Module decls) = A.Module <$> mapM checkDecl decls
