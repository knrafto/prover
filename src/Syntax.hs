module Syntax where

import Data.Text (Text)
import qualified Data.Text as Text

data Statement
    = Define Text Expr
    | Assume Text Expr
    | Prove Expr
    deriving (Show)

data Expr
    = Var Text
    | Universe
    | Pi Text Expr Expr
    | Arrow Expr Expr
    | Lam Text Expr Expr
    | App Expr [Expr]
    | Sigma Text Expr Expr
    deriving (Show)

showBinder :: Int -> String -> Text -> Expr -> Expr -> ShowS
showBinder d symbol n a b =  showParen (d > 0) $
    showString symbol .
    showString " (" .
    showString (Text.unpack n) .
    showString " : " .
    showExprPrec 0 a .
    showString "). " .
    showExprPrec 0 b

showArgs :: [Expr] -> ShowS
showArgs [] = id
showArgs [e] = showExprPrec 0 e
showArgs (e:es) = showExprPrec 1 e . showString ", " . showArgs es

showExprPrec :: Int -> Expr -> ShowS
showExprPrec _ (Var n) = showString (Text.unpack n)
showExprPrec _ Universe = showString "Type"
showExprPrec d (Pi n a b) = showBinder d "Π" n a b
showExprPrec d (Arrow a b) = showParen (d > arrowPrec) $
    showExprPrec (arrowPrec + 1) a .
    showString " → " .
    showExprPrec arrowPrec b
  where
    arrowPrec = 5
showExprPrec d (Lam n a b) = showBinder d "λ" n a b
showExprPrec d (App f args) = showParen (d > appPrec) $
    showExprPrec (appPrec + 1) f .
    showString "(" .
    showArgs args .
    showString ")"
  where
    appPrec = 10
showExprPrec d (Sigma n a b) = showBinder d "Σ" n a b

showExpr :: Expr -> String
showExpr e = showExprPrec 0 e ""