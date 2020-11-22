-- | Parses infix operators.
module Prover.InfixParser (processModule) where

import Control.Applicative
import Data.List

import Control.Monad.Combinators.Expr
import Control.Monad.State
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.Text (Text)

import Prover.Monad
import Prover.Position
import Prover.Syntax

type InfixParser = StateT [Expr Range Ident] Maybe

runInfixParser :: InfixParser a -> [Expr Range Ident] -> Maybe a
runInfixParser m es = case runStateT m es of
  Just (tree, []) -> Just tree
  _ -> Nothing

infixApp :: Expr Range Ident -> Expr Range Ident -> Expr Range Ident -> Expr Range Ident
infixApp op l r =
  EApp (rangeSpan (ann l) (ann r)) (EApp (rangeSpan (ann l) (ann op)) op l) r

satisfy :: (Expr Range Ident -> Maybe a) -> InfixParser a
satisfy p = StateT $ \case
  e:es | Just a <- p e -> Just (a, es)
  _ -> Nothing

makeParser :: HashMap Text (Fixity, Int) -> InfixParser (Expr Range Ident)
makeParser operators = makeExprParser term operatorTable
  where
    atom :: InfixParser (Expr Range Ident)
    atom = satisfy $ \case
      EVar _ n | HashMap.member (identText n) operators -> Nothing
      e -> Just e

    term :: InfixParser (Expr Range Ident)
    term =  do
      x <- atom
      rest x
      where
        rest x = app x <|> return x

        app x = do
          arg <- atom
          rest (EApp (rangeSpan (ann x) (ann arg)) x arg)

    operator :: Text -> InfixParser (Expr Range Ident -> Expr Range Ident -> Expr Range Ident)
    operator t = satisfy $ \e -> case e of
      EVar _ n | identText n == t -> Just (infixApp e)
      _ -> Nothing

    operatorsByPrecedence :: IntMap [(Text, Fixity)]
    operatorsByPrecedence = foldl' addOp IntMap.empty (HashMap.toList operators)
      where
        addOp m (n, (fixity, prec)) = IntMap.insertWith (++) prec [(n, fixity)] m

    operatorTable :: [[Operator InfixParser (Expr Range Ident)]]
    operatorTable =
      map (\ (_, ops) -> map (uncurry makeOperator) ops)
        (IntMap.toDescList operatorsByPrecedence)

    makeOperator :: Text -> Fixity -> Operator InfixParser (Expr Range Ident)
    makeOperator n = \case
      Infix  -> InfixN (operator n)
      Infixl -> InfixL (operator n)
      Infixr -> InfixR (operator n)

processExpr :: Expr Range Ident -> M (Expr Range Ident)
processExpr = \case
  EVar a n -> return $ EVar a n
  EHole a -> return $ EHole a
  EType a -> return $ EType a
  EPi a ps e -> EPi a <$> processParamGroups ps <*> processExpr e
  ELam a ps e -> ELam a <$> processParamGroups ps <*> processExpr e
  ESigma a ps e -> ESigma a <$> processParamGroups ps <*> processExpr e
  EApps r es -> do
    es' <- mapM processExpr es
    operators <- gets fixities
    case runInfixParser (makeParser operators) es' of
      Nothing -> do
        emitError $ InfixParseError r
        return $ EApps r es'
      Just e -> return e
  EApp a e1 e2 -> EApp a <$> processExpr e1 <*> processExpr e2
  EArrow a e1 e2 -> EArrow a <$> processExpr e1 <*> processExpr e2
  EPair a e1 e2 -> EPair a <$> processExpr e1 <*> processExpr e2

processParamGroup :: ParamGroup Range Ident -> M (ParamGroup Range Ident)
processParamGroup (ParamGroup ns ann) = ParamGroup ns <$> mapM processExpr ann

processParamGroups :: [ParamGroup Range Ident] -> M [ParamGroup Range Ident]
processParamGroups = mapM processParamGroup

processDecl :: Decl Range Ident -> M (Decl Range Ident)
processDecl = \case
  Define n implicits explicits ann e ->
    Define n <$> processParamGroups implicits <*> processParamGroups explicits <*> mapM processExpr ann <*> processExpr e
  Assume n implicits explicits ann ->
    Assume n <$> processParamGroups implicits <*> processParamGroups explicits <*> processExpr ann
  Rewrite n params lhs rhs ->
    Rewrite n <$> processParamGroups params <*> processExpr lhs <*> processExpr rhs
  Fixity fixity prec n -> do
    modify $ \s -> s { fixities = HashMap.insert n (fixity, prec) (fixities s) }
    return $ Fixity fixity prec n

processModule :: Module Range Ident -> M (Module Range Ident)
processModule (Module decls) = Module <$> mapM processDecl decls
