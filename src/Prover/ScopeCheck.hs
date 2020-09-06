-- | Scope-checking, where names are resolved before type-checking.
module Prover.ScopeCheck where

import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Text as Text

import Prover.Monad
import qualified Prover.Syntax.Abstract as A
import qualified Prover.Syntax.Concrete as C
import Prover.Syntax.Position

makeName :: C.Name -> TCM A.Name
makeName (C.Name t@(_, s)) = do
  nameId <- freshNameId
  let name = A.Name
        { A.nameId          = nameId
        , A.nameText        = Text.pack s
        , A.nameRange       = tokenRange t
        , A.nameBindingSite = tokenRange t
        }
  return name

-- | Add a binding to the scope.
withBinding :: A.Name -> A.BindingType -> TCM a -> TCM a
withBinding n bindingType m = do
  let binding = A.Binding
        { A.bindingNameId = A.nameId n
        , A.bindingSite   = A.nameBindingSite n
        , A.bindingType   = bindingType
        }
  local (\e -> e { tcScope = HashMap.insert (A.nameText n) binding (tcScope e) }) m

scopeCheckExpr :: C.Expr -> TCM A.Expr
scopeCheckExpr = \case
  C.Pair e1 e2                    -> scopeCheckBinop  A.Pair   e1 e2
  C.Arrow e1 e2                   -> scopeCheckBinop  A.Arrow  e1 e2
  C.Times e1 e2                   -> scopeCheckBinop  A.Times  e1 e2
  C.Equals e1 e2                  -> scopeCheckBinop  A.Equals e1 e2
  C.App e1 e2                     -> scopeCheckBinop  A.App    e1 e2
  C.Pi (C.PiKeyword t) p e        -> scopeCheckBinder A.Pi     t p e
  C.Lam (C.LamKeyword t) p e      -> scopeCheckBinder A.Lam    t p e
  C.Sigma (C.SigmaKeyword t) p e  -> scopeCheckBinder A.Sigma  t p e
  C.Id n                          -> scopeCheckName n
  C.Type (C.TypeKeyword t)        -> return $ A.Type (tokenRange t)

scopeCheckName :: C.Name -> TCM A.Expr
scopeCheckName (C.Name t@(_, s)) = do
  let r  = tokenRange t
      s' = Text.pack s
  scope <- asks tcScope
  if s == "_" then
    return $ A.Hole r
  else
    case HashMap.lookup (Text.pack s) scope of
      Nothing      -> throwError $ UnboundName r s'
      Just binding -> do
        let n = A.Name 
              { A.nameId          = A.bindingNameId binding
              , A.nameText        = s'
              , A.nameRange       = r
              , A.nameBindingSite = A.bindingSite binding
              }
        return $ case A.bindingType binding of
          A.VarBinding -> A.Var n
          A.DefBinding -> A.Def n

scopeCheckBinop
  :: (Range -> A.Expr -> A.Expr -> A.Expr)
  -> C.Expr -> C.Expr -> TCM A.Expr
scopeCheckBinop op e1 e2 = do
  e1' <- scopeCheckExpr e1
  e2' <- scopeCheckExpr e2
  return $ op (rangeSpan (getRange e1') (getRange e2')) e1' e2'

scopeCheckParam :: C.Param -> TCM (C.Name, Maybe A.Expr)
scopeCheckParam = \case
  C.TypedParam n ty -> do
    ty' <- scopeCheckExpr ty
    return (n, Just ty')
  C.UntypedParam n  -> return (n, Nothing)

scopeCheckBinder
  :: (Range -> A.Param -> A.Expr -> A.Expr)
  -> ((Int, Int), String) -> C.Param -> C.Expr -> TCM A.Expr
scopeCheckBinder binder t param e = do
  (n, ty) <- scopeCheckParam param
  n' <- makeName n
  e' <- withBinding n' A.VarBinding $ scopeCheckExpr e
  return $ binder (rangeSpan (tokenRange t) (getRange e')) (n', ty) e'

scopeCheckModule :: C.Module -> TCM A.Module
scopeCheckModule (C.Module decls) = A.Module <$> scopeCheckDecls decls

scopeCheckDecls :: [C.Decl] -> TCM [A.Decl]
scopeCheckDecls = \case
  []                       -> return []
  (C.Define param e):decls -> do
    (n, ty) <- scopeCheckParam param
    n' <- makeName n
    e' <- scopeCheckExpr e
    decls' <- withBinding n' A.DefBinding $ scopeCheckDecls decls
    return $ A.Define n' ty e' : decls'
  (C.Assume n e):decls      -> do
    n' <- makeName n
    e' <- scopeCheckExpr e
    decls' <- withBinding n' A.DefBinding $ scopeCheckDecls decls
    return $ A.Assume n' e' : decls'
