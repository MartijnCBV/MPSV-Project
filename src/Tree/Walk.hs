module Tree.Walk where
import Predicate.Solver (assertPredicate)
import Tree.Wlp (feasibleWlp)
import Tree.ProgramPath
import GCLParser.GCLDatatype
import Type (Annotate)
import Z3.Monad (Z3, Result (Sat, Unsat, Undef))
import Stats

-- simplest walk: list all complete paths
listPaths :: ControlPath -> [Stmt]
listPaths (Uni (stmt, End) next) = prependStmt stmt (listPaths next)
listPaths (Bin (cond, End, End) left right) =
  prependStmt (Assume cond) (listPaths left) ++ prependStmt (Assume (OpNeg cond)) (listPaths right)
listPaths (Bin (cond, End, _) left _) =
  prependStmt (Assume cond) (listPaths left)
listPaths (Bin (cond, _, End) _ right) =
  prependStmt (Assume (OpNeg cond)) (listPaths right)
listPaths _ = []

prependStmt :: Stmt -> [Stmt] -> [Stmt]
prependStmt stmt []    = [stmt]
prependStmt stmt stmts = map (Seq stmt) stmts

{-
keep track of
  current conjunctive wlp
  list of stmts from the last branch
when encountering branch
  add stmts to conjunctive wlp
  add branch condition (or negation thereof) to conjunctive wlp
  branch is feasible iff this new conjunctive wlp is sat
-}
walk :: Annotate -> (Stats -> Stats) -> Expr -> Stmt -> ControlPath -> Z3 ([Stmt], Stats)
walk annotate updateStats curWlp stmt next = do
  (paths, stats) <- walkPaths annotate (feasibleWlp stmt curWlp) next
  return (prependStmt stmt paths, updateStats stats)

walkPaths :: Annotate -> Expr -> ControlPath -> Z3 ([Stmt], Stats)
walkPaths _ _ (Leaf _) = pure ([], emptyStats)

-- prune unfinished branches
walkPaths _        _      (Uni (_, Unfin) _) = pure ([], unfin emptyStats)
walkPaths annotate curWlp (Bin (cond, Unfin, _) true _) = walk annotate (node . unfin) curWlp (Assume cond) true
walkPaths annotate curWlp (Bin (cond, _, Unfin) _ false) = walk annotate (node . unfin) curWlp (Assume $ OpNeg cond) false

walkPaths annotate curWlp (Uni (stmt, _) next) = walk annotate node curWlp stmt next
walkPaths annotate curWlp (Bin (cond, _, _) true false) = do
  let walkAnno = walk annotate
  let updateStats = node . path
  let trueStmt = Assume cond
  let falseStmt = Assume (OpNeg cond)
  let trueWlp  = feasibleWlp trueStmt curWlp
  let falseWlp = feasibleWlp falseStmt curWlp
  trueFeasible <- isFeasible annotate trueWlp
  if trueFeasible
  then do
    (truePaths, trueStats) <- walkAnno id curWlp trueStmt true
    falseFeasible <- isFeasible annotate falseWlp
    if falseFeasible
    then do
      (falsePaths, falseStats) <- walkAnno id curWlp falseStmt false
      return (truePaths ++ falsePaths, updateStats trueStats +++ falseStats)
    else return (truePaths, updateStats $ infeasible trueStats)
  -- if true branch is infeasible, we know that false branch must be feasible
  -- we also prune true branch in this case
  else walkAnno (updateStats . infeasible) curWlp trueStmt true

prependStmt' :: Stmt -> Z3 [Stmt] -> Z3 [Stmt]
prependStmt' stmt zStmts = do
  prependStmt stmt <$> zStmts

isFeasible :: Annotate -> Expr -> Z3 Bool
isFeasible _        (LitB True) = pure True
isFeasible annotate wlp         = do
  (result, _, _, _) <- assertPredicate (annotate wlp) [] [] []
  return $ case result of
    Undef -> error "Undef"
    Unsat -> False
    Sat   -> True

combine :: (Monad m) => (a -> a -> a) -> m a -> m a -> m a
combine comb ma1 ma2 = do a1 <- ma1; comb a1 <$> ma2

pickPaths :: Annotate -> ControlPath -> Z3 ([Stmt], Stats)
pickPaths annotate = walkPaths annotate (LitB True)
