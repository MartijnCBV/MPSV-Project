module Tree.Walk where
import Predicate.Solver (assertPredicate)
import Tree.Wlp (feasibleWlp)
import Tree.ProgramPath
import GCLParser.GCLDatatype
import Type (Annotate)
import Z3.Monad (Z3, Result (Sat, Unsat, Undef))
import Stats
import Control.Applicative

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
walkPaths annotate curWlp (Bin (cond, _, Unfin) true _) = walk annotate (node . path . unfin) curWlp (Assume cond) true
walkPaths annotate curWlp (Bin (cond, Unfin, _) _ false) = walk annotate (node . path . unfin) curWlp (Assume $ OpNeg cond) false

walkPaths annotate curWlp (Uni (stmt, _) next) = walk annotate node curWlp stmt next
walkPaths annotate curWlp (Bin (cond, _, _) true false) =
  feasible (feasibleWlp trueStmt curWlp) branchTT branchFT
  -- should work but doesn't for some reason and i've spent >2 hours on this now so fuck it
  -- feasible (feasibleWlp trueStmt curWlp) (\_ -> feasible (feasibleWlp falseStmt curWlp) branchTT branchTF) branchFT
  where feasible = isFeasible annotate
        trueStmt = Assume cond
        falseStmt = Assume (OpNeg cond)
        branchFT _ = walk annotate (node . path . infeasible) curWlp falseStmt false
        -- branchTF _ = walk annotate (node . path . infeasible) curWlp trueStmt true
        branchTT _ = liftA2 mergePaths (walk annotate id curWlp trueStmt true) (walk annotate id curWlp falseStmt false)

mergePaths :: ([Stmt], Stats) -> ([Stmt], Stats) -> ([Stmt], Stats)
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
pickPaths annotate = walkPaths annotate (LitB True)
