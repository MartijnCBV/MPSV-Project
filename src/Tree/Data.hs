{-# LANGUAGE InstanceSigs #-}
module Tree.Data where
import GCLParser.GCLDatatype (Stmt (Assume), Expr (OpNeg, Parens))

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

type ControlPath = UniBinTree Terminal Stmt (Expr, BranchType)

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

type Branch = (Expr, BranchType, Bool)
type Step = Either Stmt Branch
type Path = ([Step], Terminal)

getStmt :: Step -> Stmt
getStmt (Left stmt) = stmt
getStmt (Right (cond, _, True)) = Assume cond
getStmt (Right (cond, _, False)) = Assume $ OpNeg $ Parens cond

branch :: (Expr, BranchType) -> Bool -> Step
branch (cond, btype) dir = Right (cond, btype, dir)
