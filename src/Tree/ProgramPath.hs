module Tree.ProgramPath where

import GCLParser.GCLDatatype
import Traverse
import Tree.Data

(+:) :: Stmt -> Stmt -> Stmt
(Seq lstmt1 lstmt2) +: rstmt =
  Seq lstmt1 (lstmt2 +: rstmt)
lstmt +: rstmt         = Seq lstmt rstmt

extractPaths :: (Integral n) => n -> Stmt -> ControlPath
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

catchException' :: (Integral n) => n -> Maybe Expr -> ControlPath -> [Stmt] -> ControlPath
catchException' _ Nothing continue _ = continue
catchException' n (Just cond) continue handles = catchException n (Just cond) (show cond) continue handles

catchException :: (Integral n) => n -> Maybe Expr -> String -> ControlPath -> [Stmt] -> ControlPath
-- if there's no error condition, just continue
catchException _ Nothing _ continue _ = continue
-- when we're not in a try-catch context, throwing an exception immediately ends program execution
catchException _ (Just cond) info continue [] = Bin (cond, BExcept info) (Leaf Except) continue
-- otherwise jump to the topmost handler
catchException n (Just cond) info continue (catch : handles) = Bin (cond, BExcept info) handle continue
  where handle = extractPaths' (n - 1) (handles $+> catch)

extractPaths' :: (Integral n) => n -> (Stmt, [Stmt]) -> ControlPath
extractPaths' 0 _                       = Leaf Unfin
extractPaths' _ (stmt@Skip, _)          = Uni stmt (Leaf End)
extractPaths' _ (stmt@(Assert {}), _)   = Uni stmt (Leaf End)
extractPaths' _ (stmt@(Assume {}), _)   = Uni stmt (Leaf End)
extractPaths' n (Block _ stmt, handles) = extractPaths' n (handles $+> stmt)

extractPaths' n ass@(Assign _ expr, handles) = catchException n (errorsOn expr) (show ass) (Leaf End) handles

extractPaths' n ass@(AAssign array index expr, handles) =
  catchException n errorCond (show ass) (Leaf End) handles
  -- index out of bounds exception when assigning to index out of bounds
  where errorCond = Just $ disjunct $ indexOOB (Var array) index : toList (errorsOn expr)

extractPaths' n (IfThenElse cond thenStmt elseStmt, handles) =
  catchException' n (errorsOn cond) (Bin (cond, BIf) thenPaths elsePaths) handles
  where thenPaths = extractPaths' (n - 1) (handles $+> thenStmt)
        elsePaths = extractPaths' (n - 1) (handles $+> elseStmt)

extractPaths' n (while@(While cond body), handles) =
  catchException' n (errorsOn cond) whileBranch handles
  where whileBranch = Bin (cond, BWhile) bodyBranch (Leaf End)
        bodyBranch  = extractPaths' (n - 1) (handles $+> body +: while)

extractPaths' n (TryCatch _ try catch, handles) = extractPaths' n ((catch : handles) $+> try)

extractPaths' n (Seq (Block _ stmt1) stmt2, handles) = extractPaths' n (handles $+> stmt1 +: stmt2)

-- append statements following an if-then-else to both branches
extractPaths' n (Seq (IfThenElse cond thenStmt elseStmt) stmt, handles) =
  catchException' n (errorsOn cond) (Bin (cond, BIf) thenPaths elsePaths) handles
  where thenPaths = extractPaths' (n - 1) (handles $+> thenStmt +: stmt)
        elsePaths = extractPaths' (n - 1) (handles $+> elseStmt +: stmt)

extractPaths' n (while@(Seq (While cond body) stmt), handles) =
  catchException' n (errorsOn cond) (Bin (cond, BWhile) whilePaths exitPaths) handles
  where whilePaths = extractPaths' (n - 1) (handles $+> body +: while)
        exitPaths  = extractPaths' (n - 1) (handles $+> stmt)

extractPaths' n (Seq (TryCatch _ try catch) stmt, handles) =
  extractPaths' n (((catch +: stmt) : handles) $+> try +: stmt)

extractPaths' n (Seq ass@(Assign _ expr) stmt, handles) =
  catchException n (errorsOn expr) (show ass) continue handles
  where continue = Uni ass $ extractPaths' (n - 1) (handles $+> stmt)

extractPaths' n (Seq ass@(AAssign array index expr) stmt, handles) =
  catchException n errorCond (show ass) continue handles
  -- index out of bounds exception when assigning to index out of bounds
  where errorCond = Just $ disjunct $ indexOOB (Var array) index : toList (errorsOn expr)
        continue  = Uni ass $ extractPaths' (n - 1) (handles $+> stmt)

extractPaths' n (Seq stmt1 stmt2, handles) = Uni stmt1 (extractPaths' (n - 1) (handles $+> stmt2))

extractPaths' _ _ = error "not yet implemented"

toMaybe :: Either l r -> Maybe r
toMaybe (Right r) = Just r
toMaybe (Left _)  = Nothing

toList :: Maybe t -> [t]
toList (Just x) = [x]
toList Nothing  = []
