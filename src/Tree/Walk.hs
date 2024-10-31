module Tree.Walk where
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getFeasibleWlp)
import GCLParser.GCLDatatype
import Type (Annotate)
import Z3.Monad (Z3, Result (Sat, Unsat, Undef))
import Stats
import Control.Applicative
import Tree.Data

-- | Type of Heuristic to use and sub parameters for each type
-- Never never calls Z3
-- CheckAll always calls Z3
-- Linear calls every FLOAT steps, e.g. 1.5 calls at depth/branch_count [0, 2, 3, 5, 6, 8,...]
-- Exponential calls every FLOAT^steps, e.g. 2 calls at depth/branch_count [1, 2, 4, 8, ...]
-- UntilDepth performs a heuristic until a certain depth, afterwards it uses another heuristic
data Heuristic
    = Never
    | CheckAll WlpCheck
    | Linear Float HeuristicMeasure WlpCheck
    | Exponential Float HeuristicMeasure WlpCheck
    | UntilDepth Int Heuristic Heuristic

-- | Decides whether the heuristic should be measured against depth (which includes all statements)
-- or branches (branch depth) which only counts how many branches have occured before rather than how many statements
data HeuristicMeasure 
  = Depth
  | Branches

-- | Decides whether always both paths of a branch are checked
-- or if the other is assumed to be true if the first path checked is false 
data WlpCheck 
  = Both
  | AssumeIfFalse

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
    pathIfTrueWlpIsFalse = if assumeIfFalse heuristic
      -- if trueWlp is... ^feasible -> check if false is feasible     ^infeasible -> we know false must be feasible
      then walkFalse
      -- always check both paths in case a previous branch already made it infeasible, but this branch was not checked
      else (\_ -> feasible falseWlp walkFalse walkNone)

heuristicFunc :: Heuristic -> DepthStats -> Bool
heuristicFunc Never                               _                         = False
heuristicFunc (CheckAll _)                         _                        = True
heuristicFunc (Linear i Depth _)                  (depth, _       , prunes) = round (i * (fromIntegral prunes)) <= depth
heuristicFunc (Linear i Branches _)               (_    , branches, prunes) = round (i * (fromIntegral prunes)) <= branches
heuristicFunc (Exponential i Depth _)             (depth, _       , prunes) = round (i ^ prunes) <= depth
heuristicFunc (Exponential i Branches _)          (_    , branches, prunes) = round (i ^ prunes) <= branches
heuristicFunc (UntilDepth maxDepth untilHeuristic afterHeuristic) depthStats@(depth, _, _) = (depth <= maxDepth && before) || (depth > maxDepth && after)
  where
    before = heuristicFunc untilHeuristic depthStats
    after = heuristicFunc afterHeuristic depthStats

assumeIfFalse :: Heuristic -> Bool
assumeIfFalse Never                           = False
assumeIfFalse (CheckAll Both)                 = False
assumeIfFalse (CheckAll AssumeIfFalse)        = True
assumeIfFalse (Linear _ _ Both)               = False
assumeIfFalse (Linear _ _ AssumeIfFalse)      = True
assumeIfFalse (Exponential _ _ Both)          = False
assumeIfFalse (Exponential _ _ AssumeIfFalse) = True
assumeIfFalse (UntilDepth _ untilHeuristic _) = assumeIfFalse untilHeuristic

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
