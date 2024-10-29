module Tree.Walk where
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getFeasibleWlp)
import Tree.ProgramPath
import GCLParser.GCLDatatype
import Type (Annotate)
import Z3.Monad (Z3, Result (Sat, Unsat, Undef))
import Stats
import Control.Applicative

import Debug.Trace

debug = flip trace

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
walk :: Annotate -> (Stats -> Stats) -> [Stmt] -> Stmt -> ControlPath -> Z3 ([Stmt], Stats)
walk annotate updateStats prefix stmt next = do
  (paths, stats) <- walkPaths annotate (stmt : prefix) next
  return (prependStmt stmt paths, updateStats stats)

walkPaths :: Annotate -> [Stmt] -> ControlPath -> Z3 ([Stmt], Stats)
walkPaths _ _ (Leaf _) = pure ([], emptyStats)

-- prune unfinished branches
walkPaths _        _      (Uni (_, Unfin) _) = pure ([], unfin emptyStats)
walkPaths annotate prefix (Bin (cond, _, Unfin) true _) =
  walk annotate (node . path . unfin) prefix (Assume cond) true
walkPaths annotate prefix (Bin (cond, Unfin, _) _ false) =
  walk annotate (node . path . unfin) prefix (Assume $ OpNeg $ Parens cond) false

walkPaths annotate prefix (Uni (stmt, _) next) = walk annotate node prefix stmt next
-- prune infeasible branches
walkPaths annotate prefix (Bin (cond, _, _) true false) =
  feasible (getFeasibleWlp $ trueStmt : prefix) (\_ -> feasible (getFeasibleWlp $ falseStmt : prefix) branchTT branchTF) branchFT
  where feasible = isFeasible annotate
        trueStmt = Assume cond
        falseStmt = Assume (OpNeg $ Parens cond)
        branchFT _ = walk annotate (node . path . infeasible) prefix falseStmt false
        branchTF _ = walk annotate (node . path . infeasible) prefix trueStmt true
        branchTT _ = liftA2 mergePaths (walk annotate id prefix trueStmt true) (walk annotate id prefix falseStmt false)
        mergePaths (paths1, stats1) (paths2, stats2) = (paths1 ++ paths2, (node . path) stats1 +++ stats2)

isFeasible :: Annotate -> Expr -> (() -> Z3 ([Stmt], Stats)) -> (() -> Z3 ([Stmt], Stats)) -> Z3 ([Stmt], Stats)
isFeasible _        (LitB True) true _     = true ()
isFeasible annotate wlp         true false = do
  (result, _, _, _) <- assertPredicate (annotate wlp) [] [] []
  case result of
    Undef -> error "Undef"
    Unsat -> false ()
    Sat   -> true ()

pickPaths :: Annotate -> ControlPath -> Z3 ([Stmt], Stats)
pickPaths annotate = walkPaths annotate []
