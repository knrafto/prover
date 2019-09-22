module Syntax where

import Data.Text (Text)

type Module = [Defn]

data Defn = Defn
    { defnName :: Text
    , defnParams :: Params
    , defnType :: Expr
    , defnBody :: Expr
    } deriving (Show)

type Params = [(Text, Expr)]

data Expr
    = Var Text
    | Apply Expr [Expr]
    | Sigma Params Expr
    | Pi Params Expr
    | Lambda Params Expr
    | Equals Expr Expr
    | Arrow Expr Expr
    deriving (Show)