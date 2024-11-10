module Tree.Walk where
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getFeasibleWlp)
import Utils.Type (TypedExpr (..))
import Z3.Monad (Z3, Result (Sat, Unsat, Undef))
import Stats
import Control.Applicative
import Tree.Data
import Tree.Heuristic
import Utils.Count (sizeOf)

prependStmt :: Step -> [Path] -> [Path]
prependStmt stmt ((stmts, term) : rest) = (stmt : stmts, term) : prependStmt stmt rest
prependStmt _ [] = []

type Walker = [Action] -> ControlPath -> Z3 ([Path], Stats)

walk :: Walker -> (Stats -> Stats) -> [Action] -> Step -> ControlPath -> Z3 ([Path], Stats)
walk walker updateStats prefix step next = do
  (paths, stats) <- walker (getStmt step : prefix) next
  return (prependStmt step paths, updateStats stats)



walkPaths :: Bool -> Bool -> Heuristic -> DepthStats -> [Action] -> ControlPath -> Z3 ([Path], Stats)
walkPaths _ _ _ _ _ (Leaf Unfin) = pure ([], unfin emptyStats)
walkPaths _ _ _ _ _ (Leaf term) = pure ([([], term)], emptyStats)
walkPaths optF optB heuristic ds prefix (Uni stmt next) =
  walk (walkPaths optF optB heuristic (addDepth ds)) node prefix (Left stmt) next
walkPaths optF optB heuristic ds prefix (Bin cond true false) =
  -- prune infeasible branches if heuristic allows  
  if checkFeasibility then
    if optB then
      feasible trueWlp (\_ -> feasible falseWlp (walkBoth bothUpdate) (walkTrue bothUpdate)) (walkFalse trueUpdate)
    -- if trueWlp is... ^feasible -> check if false is feasible     ^infeasible -> we know false must be feasible
    else
    -- non-optimized: always check both
      feasible trueWlp (\_ -> feasible falseWlp (walkBoth bothUpdate2) (walkTrue bothUpdate2)) (\_ -> feasible falseWlp (walkFalse bothUpdate2) (walkNone bothUpdate2))
  else
    walkBoth id ()
  where
    doWalk = walk (walkPaths optF optB heuristic (updateDS checkFeasibility ds))
    checkFeasibility = heuristic ds trueWlp
    trueStep    = branch cond True
    falseStep   = branch cond False
    trueWlp     = getFeasibleWlp optF trueStep  prefix
    falseWlp    = getFeasibleWlp optF falseStep prefix
    trueUpdate  = addSize (sizeOf trueWlp) . feasCheck
    bothUpdate  = addSize (sizeOf trueWlp + sizeOf falseWlp) . feasCheck
    bothUpdate2 = addSize (sizeOf trueWlp + sizeOf falseWlp) . feasCheck2
    walkNone  s _ = pure ([], s emptyStats)
    walkFalse s _ = doWalk (s . node . infeasible) prefix falseStep false
    walkTrue  s _ = doWalk (s . node . infeasible) prefix trueStep true
    walkBoth  s _ = liftA2 (mergePaths s) (doWalk id prefix trueStep true) (doWalk id prefix falseStep false)
    mergePaths s (paths1, stats1) (paths2, stats2) = (paths1 ++ paths2, (s . node) stats1 +++ stats2)

feasible :: TypedExpr -> (() -> Z3 ([Path], Stats)) -> (() -> Z3 ([Path], Stats)) -> Z3 ([Path], Stats)
feasible (LitB True)  true _     = true ()
feasible (LitB False) _ false    = false ()
feasible wlp          true false = do
  (result, _, _, _) <- assertPredicate wlp [] [] []
  case result of
    Undef -> error "Undef"
    Unsat -> false ()
    Sat   -> true ()

listPaths :: Bool -> Bool -> Heuristic -> ControlPath -> Z3 ([Path], Stats)
listPaths optF optB heuristic = walkPaths optF optB heuristic (DS 0 0 0) []
