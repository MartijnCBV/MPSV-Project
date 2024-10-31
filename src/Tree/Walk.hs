module Tree.Walk where
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getFeasibleWlp)
import GCLParser.GCLDatatype
import Type (Annotate)
import Z3.Monad (Z3, Result (Sat, Unsat, Undef))
import Stats
import Control.Applicative
import Tree.Data

data Heuristic
    = CheckAll
    | Linear Int HeuristicMeasure
    | Exponential Int HeuristicMeasure
    | UntilDepth Int Heuristic

data HeuristicMeasure 
  = Depth
  | Branches

type DepthStats = (Int, Int, Int)

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
walk :: Annotate -> Heuristic -> DepthStats ->  (Stats -> Stats) -> [Stmt] -> Step -> ControlPath -> Z3 ([Path], Stats)
walk annotate heuristic depthStats updateStats prefix step next = do
  (paths, stats) <- walkPaths annotate heuristic depthStats (getStmt step : prefix) next
  return (prependStmt step paths, updateStats stats)

walkPaths :: Annotate -> Heuristic -> DepthStats-> [Stmt] -> ControlPath -> Z3 ([Path], Stats)
walkPaths _ _ _ _ (Leaf Unfin) = pure ([], unfin emptyStats)
walkPaths _ _ _ _ (Leaf term) = pure ([([], term)], emptyStats)
walkPaths annotate heuristic (depth, branches, prunes) prefix (Uni stmt next) = walk annotate heuristic (depth + 1, branches, prunes) node prefix (Left stmt) next
walkPaths annotate heuristic depthStats@(depth, branches, prunes) prefix (Bin cond true false) =
  -- prune infeasible branches if heuristic allows  
  if doPrune then 
    feasible trueWlp (\_ -> feasible falseWlp walkBoth walkTrue) pathIfTrueWlpIsFalse
  else
    walkBoth ()
  where 
    doPrune = heuristicFunc heuristic depthStats
    newDepthStats = (depth + 1, branches + 1, (if doPrune then prunes + 1 else prunes))
    feasible    = isFeasible annotate
    trueStep    = branch cond True
    falseStep   = branch cond False
    trueWlp     = getFeasibleWlp trueStep  prefix
    falseWlp    = getFeasibleWlp falseStep prefix
    walkNone _  = pure ([], emptyStats)
    walkFalse _ = walk annotate heuristic newDepthStats (node . infeasible) prefix falseStep false
    walkTrue _  = walk annotate heuristic newDepthStats (node . infeasible) prefix trueStep true
    walkBoth _  = liftA2 mergePaths (walk annotate heuristic newDepthStats id prefix trueStep true) (walk annotate heuristic newDepthStats id prefix falseStep false)
    mergePaths (paths1, stats1) (paths2, stats2) = (paths1 ++ paths2, node stats1 +++ stats2)
    pathIfTrueWlpIsFalse = case heuristic of
      -- if trueWlp is... ^feasible -> check if false is feasible     ^infeasible -> we know false must be feasible
      CheckAll -> walkFalse
      -- always check both paths in case a previous branch already made it infeasible, but this branch was not checked
      _        -> (\_ -> feasible falseWlp walkFalse walkNone)

heuristicFunc :: Heuristic -> DepthStats -> Bool
heuristicFunc CheckAll                            _                                    = True
heuristicFunc (Linear i Depth)                    (depth, _       , prunes) = prunes * i < depth
heuristicFunc (Linear i Branches)                 (_    , branches, prunes) = prunes * i < branches
heuristicFunc (Exponential i Depth)               (depth, _       , prunes) = prunes ^ i < depth
heuristicFunc (Exponential i Branches)            (_    , branches, prunes) = prunes ^ i < branches
heuristicFunc (UntilDepth maxDepth elseHeuristic) depthStats@(depth, _, _)  = depth < maxDepth && (heuristicFunc elseHeuristic depthStats)

isFeasible :: Annotate -> Expr -> (() -> Z3 ([Path], Stats)) -> (() -> Z3 ([Path], Stats)) -> Z3 ([Path], Stats)
isFeasible _        (LitB True)  true _     = true ()
isFeasible _        (LitB False) _ false    = false ()
isFeasible annotate wlp          true false = do
  (result, _, _, _) <- assertPredicate (annotate wlp) [] [] []
  case result of
    Undef -> error "Undef"
    Unsat -> false ()
    Sat   -> true ()

pickPaths :: Annotate -> Heuristic -> ControlPath -> Z3 ([Path], Stats)
pickPaths annotate heuristic = walkPaths annotate heuristic (0, 0, 0) []
