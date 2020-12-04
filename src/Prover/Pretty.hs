module Prover.Pretty where

import Control.Monad
import Data.Void
import System.IO

import Control.Monad.IO.Class
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Prettyprinter hiding (Doc, parens)
import Prettyprinter qualified as PP
import Prettyprinter.Render.Text

import Prover.Flags qualified as Flags
import Prover.Monad
import Prover.Syntax
import Prover.Term

type Doc = PP.Doc Void

debug :: Doc -> M ()
debug doc = when Flags.debug $
  liftIO $ hPutDoc stderr (doc <> line)

debugM :: M Doc -> M ()
debugM m = when Flags.debug $ do
  doc <- m
  liftIO $ hPutDoc stderr (doc <> line)

-- | Convenient infix pair (useful for debugFields) below.
(|:) :: a -> b -> (a, b)
a |: b = (a, b)

debugFields :: Doc -> [(Doc, M Doc)] -> M ()
debugFields label fields = debugM $ do
  fieldDocs <- forM fields $ \(key, m) -> do
    value <- m
    return $ fillBreak 10 (key <> ":") <> nest 10 value
  return $ label <> nest 2 (line <> vsep fieldDocs)

parens :: Bool -> M Doc -> M Doc
parens b m = do
  doc <- m
  return $ if b then "(" <> doc <> ")" else doc

subscript :: String -> Int -> Doc
subscript s i = pretty s <> pretty (map toSubscriptChar (show i))
  where
    toSubscriptChar = \case
      '0' -> '₀'
      '1' -> '₁'
      '2' -> '₂'
      '3' -> '₃'
      '4' -> '₄'
      '5' -> '₅'
      '6' -> '₆'
      '7' -> '₇'
      '8' -> '₈'
      '9' -> '₉'
      _   -> error "subscript: not a digit"

prettyVar :: Int -> Doc
prettyVar = subscript "x"

prettyMeta :: MetaId -> Doc
prettyMeta (MetaId i) = subscript "α" i

-- TODO: move this?
type MetaSubst = HashMap MetaId Term

-- | Pretty-print a context.
prettyCtx :: MetaSubst -> Ctx -> M Doc
prettyCtx _ Empty = return mempty
prettyCtx subst (Empty :> ty) = do
  tyDoc  <- prettyTerm subst Empty ty
  return $ prettyVar 0 <+> ":" <+> tyDoc
prettyCtx subst (ctx :> ty) = do
  ctxDoc <- prettyCtx subst ctx
  tyDoc  <- prettyTerm subst ctx ty
  return $ ctxDoc <> "," <+> prettyVar (ctxLength ctx) <+> ":" <+> tyDoc

-- | Pretty-print a term in a context.
prettyTerm :: MetaSubst -> Ctx -> Term -> M Doc
prettyTerm subst ctx = prettyPrec (ctxLength ctx) 0
  where
    binderPrec = 0
    commaPrec = 1
    appPrec = 10

    prettyPrec :: Int -> Int -> Term -> M Doc
    prettyPrec k d = \case
      Meta m _ args   ->
        -- TODO: code is copied from whnf implementation
        case HashMap.lookup m subst of
          Just t' -> prettyPrec k d (applyTerm t' args)
          Nothing -> lookupState m metaTerms >>= \case
            Just t' -> prettyPrec k d (applyTerm t' args)
            Nothing -> app k d (prettyMeta m) args
      Axiom n args         -> do
        n <- getState n axiomNames
        app k d (pretty (nameText n)) args
      Def n args         -> do
        n <- getState n defNames
        app k d (pretty (nameText n)) args
      Var i args           -> app k d (prettyVar (k - i - 1)) args
      Lam b                -> parens (d > binderPrec) $ do
        bDoc <- prettyPrec (k + 1) binderPrec b
        return $ "λ" <+> prettyVar k <> "." <+> bDoc
      Pair a b             -> parens (d > commaPrec) $ do
        aDoc <- prettyPrec k (commaPrec + 1) a
        bDoc <- prettyPrec k commaPrec b
        return $ aDoc <> "," <+> bDoc
      Type                 -> return "Type"
      Pi a b               -> parens (d > binderPrec) $ do
        aDoc <- prettyPrec k (appPrec + 1) a
        bDoc <- prettyPrec (k + 1) binderPrec b
        return $ "Π" <+> prettyVar k <+> ":" <+> aDoc <> "." <+> bDoc
      Sigma a b            -> parens (d > binderPrec) $ do
        aDoc <- prettyPrec k (appPrec + 1) a
        bDoc <- prettyPrec (k + 1) binderPrec b
        return $ "Σ" <+> prettyVar k <+> ":" <+> aDoc <> "." <+> bDoc

    app :: Int -> Int -> Doc -> [Term] -> M Doc
    app _ _ h []   = return h
    app k d h args = parens (d > appPrec) $ do
        argsDocs <- mapM (prettyPrec k (appPrec + 1)) args
        return $ hsep (h : argsDocs)

-- | Pretty-print a unification constraint.
prettyConstraint :: MetaSubst -> Constraint -> M Doc
prettyConstraint subst = \case
  Solved -> return "Solved"
  Inconsistent -> return "Inconsistent"
  TermEq ctx ty a b -> do
    ctxDoc <- prettyCtx subst ctx
    tyDoc <- prettyTerm subst ctx ty
    aDoc <- prettyTerm subst ctx a
    bDoc <-prettyTerm subst ctx b
    return $ ctxDoc <+> "⊢" <+> aDoc <+> "≡" <+> bDoc <+> ":" <+> tyDoc
  SpineEq ctx ty spine -> do
    ctxDoc <- prettyCtx subst ctx
    tyDoc <- prettyTerm subst ctx ty
    aDocs <- mapM (prettyTerm subst ctx . fst) spine
    bDocs <- mapM (prettyTerm subst ctx . snd) spine
    -- TODO: how exactly do we show this?
    return $ ctxDoc <+> "⊢" <+> list aDocs <+> "≡" <+> list bDocs <+> ":" <+> tyDoc
  And cs -> do
    csDocs <- mapM (prettyConstraint subst) cs
    return $ "And" <+> list csDocs
  ExactlyOne cs -> do
    csDocs <- mapM (prettyConstraint subst) cs
    return $ "ExactlyOne" <+> list csDocs
  Guarded c1 c2 -> do
    c1Doc <- prettyConstraint subst c1
    c2Doc <- prettyConstraint subst c2
    return $ "Guarded" <+> "(" <> c1Doc <> ")" <+> "(" <> c2Doc <> ")"

