module Tree.ProgramPath where

import Utils.Type
    ( Annotate,
      TypedExpr(..),
      Op(..),
      opOr,
      opLessThan,
      opGreaterThanEqual,
      opEqual )
import Tree.Data (ControlPath, UniBinTree (..), Terminal (..), BranchType (..), fromStmt, toVar)
import GCLParser.GCLDatatype (Stmt (Skip, Assert, Assume, Assign, AAssign, Seq, Block, IfThenElse, While, TryCatch), Expr)
import Utils.Traverse (traverseExpr)

(+:) :: Stmt -> Stmt -> Stmt
(Seq lstmt1 lstmt2) +: rstmt =
  Seq lstmt1 (lstmt2 +: rstmt)
lstmt +: rstmt         = Seq lstmt rstmt

extractPaths :: (Integral n) => Annotate -> n -> Stmt -> ControlPath
extractPaths annotate n stmt = extractPaths' annotate n ([] $+> stmt)

($+>) :: a -> b -> (b, a)
a $+> b = (b, a)
infixr 0 $+>

errorsOn :: TypedExpr -> Maybe TypedExpr
errorsOn expr = case traverseExpr getErrors expr of
  []              -> Nothing
  errorConditions -> Just $ disjunct errorConditions

disjunct :: [TypedExpr] -> TypedExpr
disjunct []            = undefined
disjunct [expr]        = expr
disjunct (expr : rest) = opOr expr (disjunct rest)

zero :: TypedExpr
zero = LitI 0

indexOOB' :: Annotate -> String -> Expr -> TypedExpr
indexOOB' annotate array index = case toVar annotate array of
  (_, typ) -> indexOOB (Utils.Type.Var array typ) (annotate index)

indexOOB :: TypedExpr -> TypedExpr -> TypedExpr
indexOOB array index = opOr (opLessThan index zero) (opGreaterThanEqual index (SizeOf array))

getErrors :: TypedExpr -> [TypedExpr]
-- y / x throws an exception when x == 0
getErrors (BinopExpr Divide _ divider) = [opEqual divider zero]
-- a[i] throws an exception when i < 0 or i >= #a
getErrors (ArrayElem array index) = [indexOOB array index]
-- other expressions don't throw exceptions
getErrors _ = []

catchException' :: (Integral n) => Annotate -> n -> Maybe TypedExpr -> ControlPath -> [Stmt] -> ControlPath
catchException' _ _ Nothing continue _ = continue
catchException' a n cond cont@(Bin (expr, btype) _ _) handles = catchException a n cond info cont handles
  where info = show btype ++ " " ++ show expr
catchException' _ _ _ _ _ = undefined

catchException :: (Integral n) => Annotate -> n -> Maybe TypedExpr -> String -> ControlPath -> [Stmt] -> ControlPath
-- if there's no error condition, just continue
catchException _ _ Nothing _ continue _ = continue
-- when we're not in a try-catch context, throwing an exception immediately ends program execution
catchException _ _ (Just cond) info continue [] = Bin (cond, BExcept info) (Leaf Except) continue
-- otherwise jump to the topmost handler
catchException a n (Just cond) info continue (catch : handles) = Bin (cond, BExcept info) handle continue
  where handle = extractPaths' a (n - 1) (handles $+> catch)

extractPaths' :: (Integral n) => Annotate -> n -> (Stmt, [Stmt]) -> ControlPath
extractPaths' _ 0 _                       = Leaf Unfin
extractPaths' a _ (stmt@Skip, _)          = Uni (fromStmt a stmt) (Leaf End)
extractPaths' a _ (stmt@(Assert {}), _)   = Uni (fromStmt a stmt) (Leaf End)
extractPaths' a _ (stmt@(Assume {}), _)   = Uni (fromStmt a stmt) (Leaf End)
extractPaths' a n (Block _ stmt, handles) = extractPaths' a n (handles $+> stmt)

extractPaths' a n ass@(Assign _ expr, handles) = catchException a n (errorsOn $ a expr) (show ass) (Leaf End) handles

extractPaths' a n ass@(AAssign array index expr, handles) =
  catchException a n errorCond (show ass) (Leaf End) handles
  -- index out of bounds exception when assigning to index out of bounds
  where errorCond = Just $ disjunct $ indexOOB' a array index : toList (errorsOn $ a expr)

extractPaths' a n (IfThenElse cond' thenStmt elseStmt, handles) =
  catchException' a n (errorsOn cond) (Bin (cond, BIf) thenPaths elsePaths) handles
  where cond = a cond'
        thenPaths = extractPaths' a (n - 1) (handles $+> thenStmt)
        elsePaths = extractPaths' a (n - 1) (handles $+> elseStmt)

extractPaths' a n (while@(While cond' body), handles) =
  catchException' a n (errorsOn cond) whileBranch handles
  where cond = a cond'
        whileBranch = Bin (cond, BWhile) bodyBranch (Leaf End)
        bodyBranch  = extractPaths' a (n - 1) (handles $+> body +: while)

extractPaths' a n (TryCatch _ try catch, handles) = extractPaths' a n ((catch : handles) $+> try)

extractPaths' a n (Seq (Block _ stmt1) stmt2, handles) = extractPaths' a n (handles $+> stmt1 +: stmt2)

-- append statements following an if-then-else to both branches
extractPaths' a n (Seq (IfThenElse cond' thenStmt elseStmt) stmt, handles) =
  catchException' a n (errorsOn cond) (Bin (cond, BIf) thenPaths elsePaths) handles
  where cond = a cond'
        thenPaths = extractPaths' a (n - 1) (handles $+> thenStmt +: stmt)
        elsePaths = extractPaths' a (n - 1) (handles $+> elseStmt +: stmt)

extractPaths' a n (while@(Seq (While cond' body) stmt), handles) =
  catchException' a n (errorsOn cond) (Bin (cond, BWhile) whilePaths exitPaths) handles
  where cond = a cond'
        whilePaths = extractPaths' a (n - 1) (handles $+> body +: while)
        exitPaths  = extractPaths' a (n - 1) (handles $+> stmt)

extractPaths' a n (Seq (TryCatch _ try catch) stmt, handles) =
  extractPaths' a n (((catch +: stmt) : handles) $+> try +: stmt)

extractPaths' a n (Seq ass@(Assign _ expr) stmt, handles) =
  catchException a n (errorsOn $ a expr) (show ass) continue handles
  where continue = Uni (fromStmt a ass) $ extractPaths' a (n - 1) (handles $+> stmt)

extractPaths' a n (Seq ass@(AAssign array index expr) stmt, handles) =
  catchException a n errorCond (show ass) continue handles
  -- index out of bounds exception when assigning to index out of bounds
  where errorCond = Just $ disjunct $ indexOOB' a array index : toList (errorsOn $ a expr)
        continue  = Uni (fromStmt a ass) $ extractPaths' a (n - 1) (handles $+> stmt)

extractPaths' a n (Seq stmt1 stmt2, handles) = Uni (fromStmt a stmt1) (extractPaths' a (n - 1) (handles $+> stmt2))

extractPaths' _ _ _ = error "not yet implemented"

toMaybe :: Either l r -> Maybe r
toMaybe (Right r) = Just r
toMaybe (Left _)  = Nothing

toList :: Maybe t -> [t]
toList (Just x) = [x]
toList Nothing  = []
