module Tree.Walk where
import Predicate.Solver (assertPredicate)
import Tree.Wlp (feasibleWlp)
import Tree.ProgramPath
import GCLParser.GCLDatatype
import Type (Annotate)
import Z3.Monad (Z3, Result (Sat, Unsat, Undef))

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
walkPaths :: Annotate -> Expr -> ControlPath -> Z3 [Stmt]
walkPaths _ _ (Leaf _) = pure []

-- prune unfinished branches
walkPaths _        _      (Uni (_, Unfin) _) = pure []
walkPaths annotate curWlp (Bin (cond, Unfin, _) true _) =
  prependStmt' stmt $ walkPaths annotate (feasibleWlp stmt curWlp) true
  where stmt = Assume (OpNeg cond)
walkPaths annotate curWlp (Bin (cond, _, Unfin) _ false) =
  prependStmt' stmt $ walkPaths annotate (feasibleWlp stmt curWlp) false
  where stmt = Assume cond

walkPaths annotate curWlp (Uni (stmt, _) next) = prependStmt' stmt $ walkPaths annotate (feasibleWlp stmt curWlp) next
walkPaths annotate curWlp (Bin (cond, _, _) true false) = do
  let wlp = flip feasibleWlp curWlp
  let trueStmt = Assume cond
  let falseStmt = Assume (OpNeg cond)
  let trueWlp  = wlp trueStmt
  let falseWlp = wlp falseStmt
  trueFeasible <- isFeasible annotate trueWlp
  if trueFeasible
  -- otherwise walk both branches (TODO: sometimes also check feasibility of false branch?)
  then do
    let truePaths = prependStmt' trueStmt $ walkPaths annotate trueWlp true
    let falsePaths = prependStmt' falseStmt $ walkPaths annotate falseWlp false
    combine (++) truePaths falsePaths
  -- if true branch is infeasible, we know that false branch must be feasible
  -- we also prune true branch in this case
  else prependStmt' falseStmt $ walkPaths annotate falseWlp false

prependStmt' :: Stmt -> Z3 [Stmt] -> Z3 [Stmt]
prependStmt' stmt zStmts = do
  prependStmt stmt <$> zStmts

isFeasible :: Annotate -> Expr -> Z3 Bool
isFeasible annotate wlp = do
  (result, _, _, _) <- assertPredicate (annotate wlp) [] [] []
  return $ case result of
    Undef -> error "Undef"
    Unsat -> False
    Sat   -> True

combine :: (Monad m) => (a -> a -> a) -> m a -> m a -> m a
combine comb ma1 ma2 = do a1 <- ma1; comb a1 <$> ma2

pickPaths :: Annotate -> ControlPath -> Z3 [Stmt]
pickPaths annotate = walkPaths annotate (LitB True)
