{-# LANGUAGE InstanceSigs #-}
module Tree.Data where
-- import GCLParser.GCLDatatype (Stmt (Assume, AAssign), Expr (OpNeg, Parens))
import Utils.Type (TypedExpr (OpNeg, Parens, Var), Annotate)
import GCLParser.GCLDatatype (Stmt(Skip, Assert, Assume, Assign, AAssign), Type, Expr (Var))

data UniBinTree l u b = Leaf l
  | Uni u (UniBinTree l u b)
  | Bin b (UniBinTree l u b) (UniBinTree l u b)
  deriving (Eq)

data Terminal = Except | End | Unfin
  deriving (Eq, Show)

{-
branch types:
if c
while c
except in e
-}
data BranchType = BIf | BWhile | BExcept String

instance Show BranchType where
  show :: BranchType -> String
  show BIf = "If"
  show BWhile = "While"
  show (BExcept stmt) = "Except " ++ stmt

data Action = Skip
  | Assume TypedExpr
  | Assert TypedExpr
  | Assign  (String, Type) TypedExpr
  | AAssign (String, Type) TypedExpr TypedExpr
  deriving (Show)

toVar :: Annotate -> String -> (String, Type)
toVar annotate name = case annotate $ GCLParser.GCLDatatype.Var name of
  Utils.Type.Var t n -> (t, n)
  _ -> undefined

fromStmt :: Annotate -> Stmt -> Action
fromStmt _ GCLParser.GCLDatatype.Skip = Tree.Data.Skip
fromStmt annotate (GCLParser.GCLDatatype.Assert e) = Tree.Data.Assert $ annotate e
fromStmt annotate (GCLParser.GCLDatatype.Assume e) = Tree.Data.Assume $ annotate e
fromStmt annotate (GCLParser.GCLDatatype.Assign n e) = Tree.Data.Assign (toVar annotate n) (annotate e)
fromStmt annotate (GCLParser.GCLDatatype.AAssign n i e) = Tree.Data.AAssign (toVar annotate n) (annotate i) (annotate e)
fromStmt _ stmt = error $ "Unsupported conversion from " ++ show stmt

type ControlPath = UniBinTree Terminal Action (TypedExpr, BranchType)

instance Ord Terminal where
  (<=) :: Terminal -> Terminal -> Bool
  -- order: End > Except > Unfin
  term1 <= term2 = number term1 <= number term2
                 where number :: Terminal -> Int
                       number End = 3
                       number Except = 2
                       number Unfin = 1

instance (Show l, Show u, Show b) => Show (UniBinTree l u b) where
  show :: UniBinTree l u b -> String
  show = printTree 0

printTree :: (Show l, Show u, Show b) => Int -> UniBinTree l u b -> String
printTree n (Leaf l)           = replicate (n * 2) ' ' ++ "Leaf: " ++ show l ++ "\n"
printTree n (Uni u next)       = replicate (n * 2) ' ' ++ show u ++ "\n" ++ printTree n next
printTree n (Bin b left right) = replicate (n * 2) ' ' ++ show b ++ "\n" ++ indent ++ "< LEFT >\n" ++ printTree (n + 1) left ++ indent ++ "< RIGHT >\n" ++ printTree (n + 1) right
  where indent = replicate ((n + 1) * 2) ' '

type Branch = (TypedExpr, BranchType, Bool)
type Step = Either Action Branch
type Path = ([Step], Terminal)

isExcept :: Path -> Bool
isExcept (_, Except) = True
isExcept _ = False

getStmt :: Step -> Action
getStmt (Left stmt) = stmt
getStmt (Right (cond, _, True)) = Tree.Data.Assume cond
getStmt (Right (cond, _, False)) = Tree.Data.Assume $ OpNeg $ Parens cond

branch :: (TypedExpr, BranchType) -> Bool -> Step
branch (cond, btype) dir = Right (cond, btype, dir)
