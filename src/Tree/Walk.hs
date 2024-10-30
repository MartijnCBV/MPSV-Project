module Tree.Walk where
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getFeasibleWlp)
import GCLParser.GCLDatatype
import Type (Annotate)
import Z3.Monad (Z3, Result (Sat, Unsat, Undef))
import Stats
import Control.Applicative
import Tree.Data

-- simplest walk: list all complete paths
-- listPaths :: ControlPath -> [Path]
-- listPaths (Uni stmt next) = prependStmt stmt (listPaths next)
-- listPaths (Bin cond left right) =
--   prependStmt (Assume cond) (listPaths left) ++ prependStmt (Assume (OpNeg cond)) (listPaths right)
--   where branchTo = branch 
-- listPaths (Leaf Unfin) = []
-- listPaths (Leaf term) = [([], term)]

prependStmt :: Step -> [Path] -> [Path]
prependStmt stmt ((stmts, term) : rest) = (stmt : stmts, term) : prependStmt stmt rest
prependStmt _ [] = []

{-
keep track of
  current conjunctive wlp
  list of stmts from the last branch
when encountering branch
  add stmts to conjunctive wlp
  add branch condition (or negation thereof) to conjunctive wlp
  branch is feasible iff this new conjunctive wlp is sat
-}
walk :: Annotate -> (Stats -> Stats) -> [Stmt] -> Step -> ControlPath -> Z3 ([Path], Stats)
walk annotate updateStats prefix step next = do
  (paths, stats) <- walkPaths annotate (getStmt step : prefix) next
  return (prependStmt step paths, updateStats stats)

walkPaths :: Annotate -> [Stmt] -> ControlPath -> Z3 ([Path], Stats)
walkPaths _ _ (Leaf Unfin) = pure ([], unfin emptyStats)
walkPaths _ _ (Leaf term) = pure ([([], term)], emptyStats)

walkPaths annotate prefix (Uni stmt next) = walk annotate node prefix (Left stmt) next
-- prune infeasible branches
walkPaths annotate prefix (Bin cond true false) =
  feasible trueWlp (\_ -> feasible falseWlp walkBoth walkTrue) walkFalse
  -- if true is... ^feasible -> check if false is feasible     ^infeasible -> we know false must be feasible
  where feasible    = isFeasible annotate
        trueStep    = branch cond True
        falseStep   = branch cond False
        trueWlp     = getFeasibleWlp trueStep  prefix
        falseWlp    = getFeasibleWlp falseStep prefix
        walkFalse _ = walk annotate (node . infeasible) prefix falseStep false
        walkTrue _  = walk annotate (node . infeasible) prefix trueStep true
        walkBoth _  = liftA2 mergePaths (walk annotate id prefix trueStep true) (walk annotate id prefix falseStep false)
        mergePaths (paths1, stats1) (paths2, stats2) = (paths1 ++ paths2, node stats1 +++ stats2)

isFeasible :: Annotate -> Expr -> (() -> Z3 ([Path], Stats)) -> (() -> Z3 ([Path], Stats)) -> Z3 ([Path], Stats)
isFeasible _        (LitB True)  true _     = true ()
isFeasible _        (LitB False) _ false    = false ()
isFeasible annotate wlp          true false = do
  (result, _, _, _) <- assertPredicate (annotate wlp) [] [] []
  case result of
    Undef -> error "Undef"
    Unsat -> false ()
    Sat   -> true ()

pickPaths :: Annotate -> ControlPath -> Z3 ([Path], Stats)
pickPaths annotate = walkPaths annotate []
