module Tree.Walk where
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getFeasibleWlp)
import GCLParser.GCLDatatype
import Utils.Type (Annotate)
import Z3.Monad (Z3, Result (Sat, Unsat, Undef))
import Stats
import Control.Applicative
import Tree.Data
import Tree.Heuristic

prependStmt :: Step -> [Path] -> [Path]
prependStmt stmt ((stmts, term) : rest) = (stmt : stmts, term) : prependStmt stmt rest
prependStmt _ [] = []

type Walker = [Stmt] -> ControlPath -> Z3 ([Path], Stats)

walk :: Walker -> (Stats -> Stats) -> [Stmt] -> Step -> ControlPath -> Z3 ([Path], Stats)
walk walker updateStats prefix step next = do
  (paths, stats) <- walker (getStmt step : prefix) next
  return (prependStmt step paths, updateStats stats)

walkPaths :: Bool -> Heuristic -> Annotate -> DepthStats -> [Stmt] -> ControlPath -> Z3 ([Path], Stats)
walkPaths _ _ _ _ _ (Leaf Unfin) = pure ([], unfin emptyStats)
walkPaths _ _ _ _ _ (Leaf term) = pure ([([], term)], emptyStats)
walkPaths opt heuristic annotate ds prefix (Uni stmt next) =
  walk (walkPaths opt heuristic annotate (addDepth ds)) node prefix (Left stmt) next
walkPaths opt heuristic annotate ds prefix (Bin cond true false) =
  -- prune infeasible branches if heuristic allows  
  if checkFeasibility then
    if opt then
      feasible trueWlp (\_ -> feasible falseWlp walkBoth walkTrue) walkFalse
    -- if trueWlp is... ^feasible -> check if false is feasible     ^infeasible -> we know false must be feasible
    else
    -- non-optimized: always check both
      feasible trueWlp (\_ -> feasible falseWlp walkBoth walkTrue) (\_ -> feasible falseWlp walkFalse walkNone)
  else
    walkBoth ()
  where
    doWalk = walk (walkPaths opt heuristic annotate (updateDS checkFeasibility ds))
    checkFeasibility = heuristic ds trueWlp
    feasible    = isFeasible annotate
    trueStep    = branch cond True
    falseStep   = branch cond False
    trueWlp     = getFeasibleWlp trueStep  prefix
    falseWlp    = getFeasibleWlp falseStep prefix
    walkNone _  = pure ([], emptyStats)
    walkFalse _ = doWalk (node . infeasible) prefix falseStep false
    walkTrue _  = doWalk (node . infeasible) prefix trueStep true
    walkBoth _  = liftA2 mergePaths (doWalk id prefix trueStep true) (doWalk id prefix falseStep false)
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

listPaths :: Bool -> Heuristic -> Annotate -> ControlPath -> Z3 ([Path], Stats)
listPaths opt heuristic annotate = walkPaths opt heuristic annotate (DS 0 0 0) []
