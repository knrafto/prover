module TypeCheck where

import           Control.Monad.State
import           Data.Text                      ( Text )

import qualified Syntax

type Id = Int

data Name = Name Text !Id
    deriving (Eq, Show)

data Expr
    = Var Name
    | Universe !Int
    | Apply Expr Expr
    | Sigma Name Expr Expr
    | Pi Name Expr Expr
    | Lambda Name Expr Expr
    deriving (Show)

-- Names, mapping types and optional definitions.
type Context = [(Name, (Expr, Maybe Expr))]

lookupType :: Context -> Name -> Maybe Expr
lookupType ctx n = fst <$> lookup n ctx

data TcState = TcState
    { nextId :: !Int
    , globalCtx :: Context
    } deriving (Show)

initialState :: TcState
initialState = TcState
    { nextId = 0
    , globalCtx = []
    }

-- Typechecking monad.
type TcM a = StateT TcState IO a

typeCheckStatement :: Syntax.Statement -> TcM ()
typeCheckStatement stmt = case stmt of
    Syntax.Define ident params ty body -> return ()  -- TODO
    Syntax.Assume ident ty -> return ()  -- TODO
    Syntax.Prove ty -> return ()  -- TODO

typeCheckStatements :: [Syntax.Statement] -> TcM ()
typeCheckStatements = mapM_ typeCheckStatement

typeCheck :: [Syntax.Statement] -> IO Context
typeCheck stmts = do
    (_, s) <- runStateT (typeCheckStatements stmts) initialState
    return (globalCtx s)