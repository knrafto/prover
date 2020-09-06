-- | Scope-checking, where names are resolved before type-checking.
module Prover.ScopeCheck where

import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import qualified Data.HashMap.Strict as HashMap

import Prover.Monad
import qualified Prover.Syntax.Abstract as A
import qualified Prover.Syntax.Concrete as C
import Prover.Syntax.Position

makeName :: C.Name -> TCM A.Name
makeName (C.Name r s) = do
  nameId <- freshNameId
  let name = A.Name
        { A.nameId          = nameId
        , A.nameText        = s
        , A.nameRange       = r
        , A.nameBindingSite = r
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
  C.Id      n       -> scopeCheckId n
  C.Hole    r       -> return $ A.Hole r
  C.Type    r       -> return $ A.Type r
  C.Pi      r p e   -> scopeCheckBinder A.Pi     r p e
  C.Lam     r p e   -> scopeCheckBinder A.Lam    r p e
  C.Sigma   r p e   -> scopeCheckBinder A.Sigma  r p e
  C.App     r e1 e2 -> scopeCheckBinop  A.App    r e1 e2
  C.Arrow   r e1 e2 -> scopeCheckBinop  A.Arrow  r e1 e2
  C.Times   r e1 e2 -> scopeCheckBinop  A.Times  r e1 e2
  C.Equals  r e1 e2 -> scopeCheckBinop  A.Equals r e1 e2
  C.Pair    r e1 e2 -> scopeCheckBinop  A.Pair   r e1 e2

scopeCheckId :: C.Name -> TCM A.Expr
scopeCheckId (C.Name r s) = do
  scope <- asks tcScope
  case HashMap.lookup s scope of
    Nothing      -> throwError $ UnboundName r s
    Just binding -> do
      let n = A.Name 
            { A.nameId          = A.bindingNameId binding
            , A.nameText        = s
            , A.nameRange       = r
            , A.nameBindingSite = A.bindingSite binding
            }
      return $ case A.bindingType binding of
        A.VarBinding   -> A.Var n
        A.DefBinding   -> A.Def n
        A.AxiomBinding -> A.Axiom n

scopeCheckBinder
  :: (Range -> A.Param -> A.Expr -> A.Expr)
  -> Range -> C.Param -> C.Expr -> TCM A.Expr
scopeCheckBinder binder r (n, ty) e = do
  n' <- makeName n
  ty' <- mapM scopeCheckExpr ty
  e' <- withBinding n' A.VarBinding $ scopeCheckExpr e
  return $ binder r (n', ty') e'

scopeCheckBinop
  :: (Range -> A.Expr -> A.Expr -> A.Expr)
  -> Range -> C.Expr -> C.Expr -> TCM A.Expr
scopeCheckBinop op r e1 e2 = do
  e1' <- scopeCheckExpr e1
  e2' <- scopeCheckExpr e2
  return $ op r e1' e2'

scopeCheckModule :: C.Module -> TCM A.Module
scopeCheckModule (C.Module decls) = A.Module <$> scopeCheckDecls decls

scopeCheckDecls :: [C.Decl] -> TCM [A.Decl]
scopeCheckDecls = \case
  []                      -> return []
  (C.Define n ty e):decls -> do
    n' <- makeName n
    ty' <- mapM scopeCheckExpr ty
    e' <- scopeCheckExpr e
    decls' <- withBinding n' A.DefBinding $ scopeCheckDecls decls
    return $ A.Define n' ty' e' : decls'
  (C.Assume n e):decls     -> do
    n' <- makeName n
    e' <- scopeCheckExpr e
    decls' <- withBinding n' A.AxiomBinding $ scopeCheckDecls decls
    return $ A.Assume n' e' : decls'
