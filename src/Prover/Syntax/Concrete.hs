module Prover.Syntax.Concrete
  ( module Prover.Syntax.Concrete.Abs
  , parse
  , printTree
  ) where

import Prover.Syntax.Concrete.Abs
import Prover.Syntax.Concrete.ErrM
import Prover.Syntax.Concrete.Layout
import Prover.Syntax.Concrete.Par
import Prover.Syntax.Concrete.Print

parse :: String -> Either String Module
parse s = case pModule (resolveLayout True (myLexer s)) of
  Bad err -> Left err
  Ok expr -> Right expr
