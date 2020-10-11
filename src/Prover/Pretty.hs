module Prover.Pretty where

import Control.Monad
import Data.Void
import System.IO

import Control.Monad.IO.Class
import Prettyprinter hiding (Doc, parens)
import Prettyprinter qualified as PP
import Prettyprinter.Render.Text
import Prover.Monad ( getState, M, State(axiomNames) )
import Prover.Syntax.Abstract qualified as A
import Prover.Term

import Flags qualified

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
    return $ fillBreak 8 (key <> ":") <> nest 8 value
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
prettyVar i = subscript "x" i

prettyMeta :: MetaId -> Doc
prettyMeta (MetaId i) = subscript "α" i

-- | Pretty-print a term in a context.
prettyTerm :: Ctx -> Term -> M Doc
prettyTerm ctx = prettyPrec (ctxLength ctx) 0
  where
    binderPrec = 0
    commaPrec = 1
    appPrec = 10

    prettyPrec :: Int -> Int -> Term -> M Doc
    prettyPrec k d = \case
      BlockedMeta m args   -> app k d (prettyMeta m) args
      BlockedAxiom n args  -> do
        n <- getState n axiomNames
        app k d (pretty (A.nameText n)) args
      Axiom n args         -> do
        n <- getState n axiomNames
        app k d (pretty (A.nameText n)) args
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

-- | Pretty-print a context.
prettyCtx :: Ctx -> M Doc
prettyCtx C0          = return mempty
prettyCtx (C0  :> ty) = do
  tyDoc  <- prettyTerm C0 ty
  return $ prettyVar 0 <+> ":" <+> tyDoc
prettyCtx (ctx :> ty) = do
  ctxDoc <- prettyCtx ctx
  tyDoc  <- prettyTerm ctx ty
  return $ ctxDoc <> line <> prettyVar (ctxLength ctx) <+> ":" <+> tyDoc
