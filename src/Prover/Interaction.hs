-- | Syntax highlighting and error messages.
module Prover.Interaction where

import Data.Aeson
import Data.Text (Text)
import qualified Data.Text as Text

import Prover.Monad
import Prover.Syntax.Abstract
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

highlightExpr :: Expr -> [HighlightedRange]
highlightExpr = \case
  Var     _ n     -> [HighlightedRange (getRange n) HighlightVarName]
  Def     _ n     -> [HighlightedRange (getRange n) HighlightDefName]
  Axiom   _ n     -> [HighlightedRange (getRange n) HighlightAxiomName]
  Hole    i       -> [HighlightedRange (getRange i) HighlightHole]
  Type    i       -> [HighlightedRange (getRange i) HighlightType]
  Pi      _ b e   -> highlightBinding b HighlightVarName ++ highlightExpr e
  Lam     _ b e   -> highlightBinding b HighlightVarName ++ highlightExpr e
  Sigma   _ b e   -> highlightBinding b HighlightVarName ++ highlightExpr e
  App     _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  Arrow   _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  Times   _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  Equals  _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  Pair    _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2

highlightBinding :: Binding -> HighlightKind -> [HighlightedRange]
highlightBinding (Binding n _ ann) kind =
  HighlightedRange (nameRange n) kind : foldMap highlightExpr ann

highlightDecl :: Decl -> [HighlightedRange]
highlightDecl = \case
  Define b e -> highlightBinding b HighlightDefName ++ highlightExpr e
  Assume b   -> highlightBinding b HighlightAxiomName

highlightModule :: Module -> [HighlightedRange]
highlightModule (Module decls) = concatMap highlightDecl decls

quote :: Text -> String
quote t = "'" ++ Text.unpack t ++ "'"

-- TODO: Move Err type into Prover.Errors, provide getRange and errorMessage
diagnoseErr :: Err -> Diagnostic
diagnoseErr = \case
  UnboundName r n     -> Diagnostic r $ "unbound name " ++ quote n
  MissingBuiltin r n  -> Diagnostic r $ "missing built-in " ++ quote n
  -- TODO: pretty-print expression
  CannotApply e       -> Diagnostic (getRange e) "expression cannot be applied to args"
  Unimplemented r s   -> Diagnostic r $ "unimplemented: " ++ s