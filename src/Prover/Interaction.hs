-- | Syntax highlighting and error messages.
module Prover.Interaction where

import Data.Aeson
import Data.Text (Text)
import Data.Text qualified as Text

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
  | HighlightUnboundName
  | HighlightHole
  | HighlightType
  deriving (Show)

instance ToJSON HighlightKind where
  toJSON = \case
    HighlightVarName      -> "var_name"
    HighlightDefName      -> "def_name"
    HighlightAxiomName    -> "axiom_name"
    HighlightUnboundName  -> "unbound_name"
    HighlightHole         -> "hole"
    HighlightType         -> "type"

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
  Var     i _     -> [HighlightedRange (getRange i) HighlightVarName]
  Def     i _     -> [HighlightedRange (getRange i) HighlightDefName]
  Axiom   i _     -> [HighlightedRange (getRange i) HighlightAxiomName]
  Unbound i _     -> [HighlightedRange (getRange i) HighlightUnboundName]
  Hole    i       -> [HighlightedRange (getRange i) HighlightHole]
  Type    i       -> [HighlightedRange (getRange i) HighlightType]
  Pi      _ p e   -> highlightParam HighlightVarName p ++ highlightExpr e
  Lam     _ p e   -> highlightParam HighlightVarName p ++ highlightExpr e
  Sigma   _ p e   -> highlightParam HighlightVarName p ++ highlightExpr e
  App     _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  Arrow   _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  Times   _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  Equals  _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  Pair    _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2

highlightParam :: HighlightKind -> Param -> [HighlightedRange]
highlightParam kind (Param n _ ann) =
  HighlightedRange (nameRange n) kind : foldMap highlightExpr ann

highlightDecl :: Decl -> [HighlightedRange]
highlightDecl = \case
  Define params def e ->
    concatMap (highlightParam HighlightVarName) params ++
    highlightParam HighlightDefName def ++
    highlightExpr e
  Assume params def ->
    concatMap (highlightParam HighlightVarName) params ++
    highlightParam HighlightAxiomName def

highlightModule :: Module -> [HighlightedRange]
highlightModule (Module decls) = concatMap highlightDecl decls

quote :: Text -> String
quote t = "'" ++ Text.unpack t ++ "'"

-- TODO: Move Error type into Prover.Errors, provide getRange and errorMessage
diagnoseError :: Error -> Diagnostic
diagnoseError = \case
  UnboundName r n       -> Diagnostic r $ "unbound name " ++ quote n
  TypeError r           -> Diagnostic r $ "type error"
  UnsolvedConstraint r  -> Diagnostic r $ "unsolved constraint"
  UnsolvedMeta r _      -> Diagnostic r $ "unsolved meta"
