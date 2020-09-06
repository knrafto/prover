module Prover.Syntax.Concrete
  ( module Prover.Syntax.Concrete.Abs
  , parse
  , printTree
  ) where

import Prover.Syntax.Concrete.Abs
import Prover.Syntax.Concrete.ErrM
import Prover.Syntax.Concrete.Par
import Prover.Syntax.Concrete.Print

parse :: String -> Either String Expr
parse s = case pExpr (myLexer s) of
  Bad err -> Left err
  Ok expr -> Right expr
