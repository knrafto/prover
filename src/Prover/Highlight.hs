-- | Syntax highlighting.
module Prover.Highlight where

import Data.Aeson

import qualified Prover.Syntax.Abstract as A
import Prover.Syntax.Position

data HighlightKind
  = HighlightVarName
  | HighlightDefName
  | HighlightAxiomName
  | HighlightHole
  | HighlightType
  deriving (Show)

instance ToJSON HighlightKind where
  toJSON = \case
    HighlightVarName    -> "var_name"
    HighlightDefName    -> "def_name"
    HighlightAxiomName  -> "axiom_name"
    HighlightHole       -> "hole"
    HighlightType       -> "type"

data HighlightedRange = HighlightedRange Range HighlightKind
  deriving (Show)

instance ToJSON HighlightedRange where
  toJSON (HighlightedRange r k) = object ["range" .= r, "kind" .= k]

highlightExpr :: A.Expr -> [HighlightedRange]
highlightExpr = \case
  A.Var     n       -> [HighlightedRange (A.nameRange n) HighlightVarName]
  A.Def     n       -> [HighlightedRange (A.nameRange n) HighlightDefName]
  A.Axiom   n       -> [HighlightedRange (A.nameRange n) HighlightAxiomName]
  A.Hole    r       -> [HighlightedRange r HighlightHole]
  A.Type    r       -> [HighlightedRange r HighlightType]
  A.Pi      _ p e   -> highlightParam p ++ highlightExpr e
  A.Lam     _ p e   -> highlightParam p ++ highlightExpr e
  A.Sigma   _ p e   -> highlightParam p ++ highlightExpr e
  A.App     _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  A.Arrow   _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  A.Times   _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  A.Equals  _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  A.Pair    _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2

highlightParam :: A.Param -> [HighlightedRange]
highlightParam (n, ty) =
  HighlightedRange (A.nameRange n) HighlightVarName :
    foldMap highlightExpr ty

highlightDecl :: A.Decl -> [HighlightedRange]
highlightDecl = \case
  A.Define n ty e ->
    HighlightedRange (A.nameRange n) HighlightDefName :
      foldMap highlightExpr ty ++ highlightExpr e
  A.Assume n ty   ->
    HighlightedRange (A.nameRange n) HighlightAxiomName :
      highlightExpr ty

highlightModule :: A.Module -> [HighlightedRange]
highlightModule (A.Module decls) = concatMap highlightDecl decls
