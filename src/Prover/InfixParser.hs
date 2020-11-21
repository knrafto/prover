-- | Parses infix operators.
module Prover.InfixParser where

import Control.Applicative
import Data.List
import System.Exit

import Control.Monad.Combinators.Expr
import Control.Monad.IO.Class
import Control.Monad.State
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.Text (Text)
import Prettyprinter

import Prover.Monad
import Prover.Pretty
import Prover.Syntax.Concrete
import Prover.Syntax.Position

type InfixParser = StateT [Expr] Maybe

runInfixParser :: InfixParser a -> [Expr] -> Maybe a
runInfixParser m es = case runStateT m es of
  Just (tree, []) -> Just tree
  _               -> Nothing

data InfixTree
  = Atom Expr
  | App Range InfixTree InfixTree
  deriving (Show)

instance HasRange InfixTree where
  getRange = \case
    Atom e    -> getRange e
    App r _ _ -> r

infixApp :: InfixTree -> InfixTree -> InfixTree -> InfixTree
infixApp op l r =
  App (rangeSpan (getRange l) (getRange r))
    (App (rangeSpan (getRange l) (getRange op)) op l)
    r

satisfy :: (Expr -> Maybe a) -> InfixParser a
satisfy p = StateT $ \case
  (e:es)
    | Just a <- p e -> Just (a, es)
  _                 -> Nothing

makeParser :: HashMap Text (Fixity, Int) -> InfixParser InfixTree
makeParser operators = makeExprParser term operatorTable
  where
    atom :: InfixParser InfixTree
    atom = satisfy $ \case
      Id n | HashMap.member (nameText n) operators -> Nothing
      e                                            -> Just (Atom e)

    term :: InfixParser InfixTree
    term =  do
      x <- atom
      rest x
      where
        rest x = app x <|> return x

        app x = do
          arg <- atom
          rest (App (rangeSpan (getRange x) (getRange arg)) x arg)

    operator :: Text -> InfixParser (InfixTree -> InfixTree -> InfixTree)
    operator t = satisfy $ \e -> case e of
      Id n | nameText n == t -> Just (infixApp (Atom e))
      _                      -> Nothing

    operatorsByPrecedence :: IntMap [(Text, Fixity)]
    operatorsByPrecedence = foldl' addOp IntMap.empty (HashMap.toList operators)
      where
        addOp m (n, (fixity, prec)) = IntMap.insertWith (++) prec [(n, fixity)] m

    operatorTable :: [[Operator InfixParser InfixTree]]
    operatorTable =
      map (\ (_, ops) -> map (uncurry makeOperator) ops)
        (IntMap.toDescList operatorsByPrecedence)

    makeOperator :: Text -> Fixity -> Operator InfixParser InfixTree
    makeOperator n = \case
      Infix  -> InfixN (operator n)
      Infixl -> InfixL (operator n)
      Infixr -> InfixR (operator n)

parseInfixOperators :: Range -> [Expr] -> M InfixTree
parseInfixOperators r es = do
  operators <- gets fixities
  case runInfixParser (makeParser operators) es of
    -- TODO: error recovery
    Nothing -> do
      debug $ pretty r <> ": error parsing infix operators"
      liftIO exitFailure
    Just tree -> return tree
