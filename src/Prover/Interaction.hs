-- | Syntax highlighting and error messages.
module Prover.Interaction where

import Data.Aeson
import Data.Text (Text)
import qualified Data.Text as Text

import Prover.Monad
import qualified Prover.Syntax.Abstract as A
import Prover.Syntax.Position

data Response = Response
  { highlighting :: [HighlightedRange]
  , diagnostics  :: [Diagnostic]
  }
  deriving (Show)

instance ToJSON Response where
  toJSON r = object ["highlighting" .= highlighting r, "diagnostics" .= diagnostics r]

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

data Diagnostic = Diagnostic
  { diagnosticRange :: Range
  , diagnosticMessage :: String
  }
  deriving (Show)

instance ToJSON Diagnostic where
  toJSON (Diagnostic r m) = object ["range" .= r, "message" .= m]

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

quote :: Text -> String
quote t = "'" ++ Text.unpack t ++ "'"

errorDiagnostic :: TCError -> Diagnostic
errorDiagnostic = \case
  UnboundName r e -> Diagnostic r $ "unbound name " ++ quote e
