-- | Syntax highlighting and error messages.
module Prover.Interaction where

import Data.Aeson
import Data.Text (Text)
import Data.Text qualified as Text

import Prover.Monad
import Prover.Position
import Prover.Syntax

data Response = Response
  { highlighting :: [HighlightedRange]
  , diagnostics  :: [Diagnostic]
  }
  deriving (Show)

instance ToJSON Response where
  toJSON r = object ["highlighting" .= highlighting r, "diagnostics" .= diagnostics r]

data HighlightKind
  = HighlightLocalName
  | HighlightDefName
  | HighlightAxiomName
  | HighlightRewriteName
  | HighlightUnboundName
  | HighlightHole
  | HighlightGoal
  | HighlightType
  deriving (Show)

instance ToJSON HighlightKind where
  toJSON = \case
    HighlightLocalName    -> "local_name"
    HighlightDefName      -> "def_name"
    HighlightAxiomName    -> "axiom_name"
    HighlightRewriteName  -> "rewrite_name"
    HighlightUnboundName  -> "unbound_name"
    HighlightHole         -> "hole"
    HighlightGoal         -> "goal"
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

highlightExpr :: Expr ExprInfo Name -> [HighlightedRange]
highlightExpr = \case
  EVar     _ n     -> highlightName n
  EHole    i       -> [HighlightedRange (exprInfoRange i) HighlightHole]
  EGoal    i _     -> [HighlightedRange (exprInfoRange i) HighlightGoal]
  EType    i       -> [HighlightedRange (exprInfoRange i) HighlightType]
  EPi      _ ps e  -> highlightParamGroups ps ++ highlightExpr e
  ELam     _ ps e  -> highlightParamGroups ps ++ highlightExpr e
  ESigma   _ ps e  -> highlightParamGroups ps ++ highlightExpr e
  EApps    _ es    -> concatMap highlightExpr es
  EApp     _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  EArrow   _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2
  EPair    _ e1 e2 -> highlightExpr e1 ++ highlightExpr e2

highlightName :: Name -> [HighlightedRange]
highlightName n = [HighlightedRange (nameRange n) kind]
  where
    kind = case nameReferent n of
      LocalName _ -> HighlightLocalName
      DefName _ -> HighlightDefName
      AxiomName _ -> HighlightAxiomName
      RewriteName -> HighlightRewriteName
      UnboundName -> HighlightUnboundName

highlightParamGroup :: ParamGroup ExprInfo Name -> [HighlightedRange]
highlightParamGroup (ParamGroup ns ann) =
  concatMap highlightName ns ++ foldMap highlightExpr ann

highlightParamGroups :: [ParamGroup ExprInfo Name] -> [HighlightedRange]
highlightParamGroups = concatMap highlightParamGroup

highlightDecl :: Decl ExprInfo Name -> [HighlightedRange]
highlightDecl = \case
  Define n implicits explicits ann e ->
    highlightName n ++
    highlightParamGroups implicits ++
    highlightParamGroups explicits ++
    foldMap highlightExpr ann ++
    highlightExpr e
  Assume n implicits explicits ann ->
    highlightName n ++
    highlightParamGroups implicits ++
    highlightParamGroups explicits ++
    highlightExpr ann
  Rewrite n params lhs rhs ->
    highlightName n ++
    highlightParamGroups params ++
    highlightExpr lhs ++
    highlightExpr rhs
  Fixity{} -> []  -- TODO: highlight?

highlightModule :: Module ExprInfo Name -> [HighlightedRange]
highlightModule (Module decls) = concatMap highlightDecl decls

quote :: Text -> String
quote t = "'" ++ Text.unpack t ++ "'"

-- TODO: Move Error type into Prover.Errors, provide getRange and errorMessage
diagnoseError :: Error -> Diagnostic
diagnoseError = \case
  UnboundNameError r n     -> Diagnostic r ("unbound name " ++ quote n)
  UnsolvedConstraint r     -> Diagnostic r "unsolved constraint"
  UnsolvedMeta r _         -> Diagnostic r "unsolved meta"
  BadPattern r             -> Diagnostic r "expression not allowed in pattern"
  MissingPatternVariable r -> Diagnostic r "missing variable in pattern"
  LateImplicitParam r _    -> Diagnostic r "implicit parameters must precede any explicit parameters"
  InfixParseError r        -> Diagnostic r "could not parse infix operators"
  FoundGoal r _            -> Diagnostic r "found goal"
