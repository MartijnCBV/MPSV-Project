{-# LANGUAGE InstanceSigs #-}
module Tree.ProgramPath where

import GCLParser.GCLDatatype
import GCLParser.Parser ( parseGCLfile )
import Traverse

data UniBinTree u b = Leaf
  | Uni u (UniBinTree u b)
  | Bin b (UniBinTree u b) (UniBinTree u b)
  deriving (Eq)

type ControlPath = UniBinTree Stmt Expr

instance (Show u, Show b) => Show (UniBinTree u b) where
  show :: UniBinTree u b -> String
  show = printTree 0

-- instance (Eq u, Eq b) => Eq (UniBinTree u b) where
--   (==) :: (Eq u, Eq b) => UniBinTree u b -> UniBinTree u b -> Bool
--   Leaf             == Leaf             = True
--   (Uni val1 rest1) == (Uni val2 rest2) = val1 == val2 && rest1 == rest2
--   (Bin val1 l1 r1) == (Bin val2 l2 r2) = val1 == val2 && l1 == l2 && r1 == r2
--   _                == _                = False

printTree :: (Show u, Show b) => Int -> UniBinTree u b -> String
printTree n Leaf               = replicate (n * 2) ' ' ++ "Leaf\n"
printTree n (Uni u next)       = replicate (n * 2) ' ' ++ show u ++ "\n" ++ printTree n next
printTree n (Bin b left right) = replicate (n * 2) ' ' ++ show b ++ "\n" ++ indent ++ "< LEFT >\n" ++ printTree (n + 1) left ++ indent ++ "< RIGHT >\n" ++ printTree (n + 1) right
  where indent = replicate ((n + 1) * 2) ' '

(+:) :: Stmt -> Stmt -> Stmt
(Seq lstmt1 lstmt2) +: rstmt =
  Seq lstmt1 (lstmt2 +: rstmt)
lstmt +: rstmt         = Seq lstmt rstmt

controlLeaf :: Stmt -> ControlPath
controlLeaf stmt = Uni stmt Leaf

extractPaths :: Int -> Stmt -> ControlPath
extractPaths n stmt = extractPaths' n ([] $+> stmt)

($+>) :: a -> b -> (b, a)
a $+> b = (b, a)
infixr 0 $+>

errorsOn :: Expr -> Maybe Expr
errorsOn expr = case traverseExpr getErrors expr of
  []              -> Nothing
  errorConditions -> Just $ disjunct errorConditions

disjunct :: [Expr] -> Expr
disjunct []            = undefined
disjunct [expr]        = expr
disjunct (expr : rest) = opOr expr (disjunct rest)

zero :: Expr
zero = LitI 0

indexOOB :: Expr -> Expr -> Expr
indexOOB array index = opOr (opLessThan index zero) (opGreaterThanEqual index (SizeOf array))

getErrors :: Expr -> [Expr]
-- y / x throws an exception when x == 0
getErrors (BinopExpr Divide _ divider) = [opEqual divider zero]
-- a[i] throws an exception when i < 0 or i >= #a
getErrors (ArrayElem array index) = [indexOOB array index]
-- other expressions don't throw exceptions
getErrors _ = []

catchException :: Int -> Maybe Expr -> ControlPath -> [Stmt] -> ControlPath
-- if there's no error condition, just continue
catchException _ Nothing continue _ = continue
-- when we're not in a try-catch context, throwing an exception immediately ends program execution
catchException _ (Just cond) continue [] = Bin cond Leaf continue
-- otherwise jump to the topmost handler
catchException n (Just cond) continue (catch : handles) = Bin cond (extractPaths' (n - 1) (handles $+> catch)) continue

extractPaths' :: Int -> (Stmt, [Stmt]) -> ControlPath
extractPaths' 0 _                       = Leaf
extractPaths' _ (stmt@Skip, _)          = controlLeaf stmt
extractPaths' _ (stmt@(Assert {}), _)   = controlLeaf stmt
extractPaths' _ (stmt@(Assume {}), _)   = controlLeaf stmt
extractPaths' n (Block _ stmt, handles) = extractPaths' n (handles $+> stmt)

extractPaths' n (stmt@(Assign _ expr), handles) = catchException n (errorsOn expr) (controlLeaf stmt) handles

extractPaths' n (stmt@(AAssign array index expr), handles) =
  catchException n errorCond (controlLeaf stmt) handles
  -- index out of bounds exception when assigning to index out of bounds
  where errorCond = Just $ disjunct $ indexOOB (Var array) index : toList (errorsOn expr)

extractPaths' n (IfThenElse cond thenStmt elseStmt, handles) =
  catchException n (errorsOn cond) (Bin cond thenPaths elsePaths) handles
  where thenPaths = extractPaths' (n - 1) (handles $+> thenStmt)
        elsePaths = extractPaths' (n - 1) (handles $+> elseStmt)

extractPaths' n (while@(While cond body), handles) =
  catchException n (errorsOn cond) whileBranch handles
  where whileBranch = Bin cond (extractPaths' (n - 1) (handles $+> body +: while)) Leaf

extractPaths' n (TryCatch _ try catch, handles) = extractPaths' n ((catch : handles) $+> try)

extractPaths' n (Seq (Block _ stmt1) stmt2, handles) = extractPaths' n (handles $+> (stmt1 +: stmt2))

-- append statements following an if-then-else to both branches
extractPaths' n (Seq (IfThenElse cond thenStmt elseStmt) stmt, handles) =
  catchException n (errorsOn cond) (Bin cond thenPaths elsePaths) handles
  where thenPaths = extractPaths' (n - 1) (handles $+> thenStmt +: stmt)
        elsePaths = extractPaths' (n - 1) (handles $+> elseStmt +: stmt)

extractPaths' n (while@(Seq (While cond body) stmt), handles) =
  catchException n (errorsOn cond) (Bin cond whilePaths exitPaths) handles
  where whilePaths = extractPaths' (n - 1) (handles $+> (body +: while))
        exitPaths  = extractPaths' (n - 1) (handles $+> stmt)

extractPaths' n (Seq (TryCatch _ try catch) stmt, handles) =
  extractPaths' n (((catch +: stmt) : handles) $+> try +: stmt)

extractPaths' n (Seq ass@(Assign _ expr) stmt, handles) = catchException n (errorsOn expr) continue handles
  where continue = Uni ass (extractPaths' (n - 1) (handles $+> stmt))

extractPaths' n (Seq ass@(AAssign array index expr) stmt, handles) =
  catchException n errorCond continue handles
  -- index out of bounds exception when assigning to index out of bounds
  where errorCond = Just $ disjunct $ indexOOB (Var array) index : toList (errorsOn expr)
        continue  = Uni ass (extractPaths' (n - 1) (handles $+> stmt))

extractPaths' n (Seq stmt1 stmt2, handles) = Uni stmt1 (extractPaths' (n - 1) (handles $+> stmt2))

extractPaths' _ _ = error "not yet implemented"

toMaybe :: Either l r -> Maybe r
toMaybe (Right r) = Just r
toMaybe (Left _)  = Nothing

toList :: Maybe t -> [t]
toList (Just x) = [x]
toList Nothing  = []

listPaths :: ControlPath -> [Stmt]
listPaths Leaf = []
listPaths (Uni stmt next) = prependStmt stmt (listPaths next)
listPaths (Bin cond left right) =
  prependStmt (Assume cond) (listPaths left) ++ prependStmt (Assume (OpNeg cond)) (listPaths right)

prependStmt :: Stmt -> [Stmt] -> [Stmt]
prependStmt stmt []    = [stmt]
prependStmt stmt stmts = map (Seq stmt) stmts

testExtract :: Int -> String -> IO (Maybe ControlPath)
testExtract n file = do
  gcl <- parseGCLfile file
  return $ fmap (extractPaths n . stmt) (toMaybe gcl)
