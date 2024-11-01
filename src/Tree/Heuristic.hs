module Tree.Heuristic where

type Heuristic = DepthStats -> Bool

-- | Type of Heuristic to use and sub parameters for each type
-- never never calls Z3
-- checkAll always calls Z3
-- linear calls every FLOAT steps, e.g. 1.5 calls at depth/branch_count [0, 2, 3, 5, 6, 8,...]
-- exponential calls every FLOAT^steps, e.g. 2 calls at depth/branch_count [1, 2, 4, 8, ...]
-- untilDepth performs a heuristic until a certain depth, after which feasibility isn't checked anymore
-- switchDepth switches between two heuristics based on the depth 

never :: Heuristic
never _ = False

checkAll :: Heuristic
checkAll _ = True

linear :: Float -> HeuristicMeasure -> Heuristic
linear i Depth    (DS depth _        prunes) = round (i * fromIntegral prunes) <= depth
linear i Branches (DS _     branches prunes) = round (i * fromIntegral prunes) <= branches

exponential :: Float -> HeuristicMeasure -> Heuristic
exponential i Depth    (DS depth _        prunes) = round (i ^ prunes) <= depth
exponential i Branches (DS _     branches prunes) = round (i ^ prunes) <= branches

untilDepth :: Int -> HeuristicMeasure -> Heuristic -> Heuristic
untilDepth d Depth    heur ds@DS{depth=depth}       = depth < d && heur ds
untilDepth d Branches heur ds@DS{branches=branches} = branches < d && heur ds

switchDepth :: Int -> HeuristicMeasure -> Heuristic -> Heuristic -> Heuristic
switchDepth m Depth    before after ds@DS{depth=depth}       = (depth <= m && before ds) || (depth > m && after ds)
switchDepth m Branches before after ds@DS{branches=branches} = (branches <= m && before ds) || (branches > m && after ds)


-- | Decides whether the heuristic should be measured against depth (which includes all statements)
-- or branches (branch depth) which only counts how many branches have occured before rather than how many statements
data HeuristicMeasure 
  = Depth
  | Branches

data DepthStats = DS { depth :: Int, branches :: Int, prunes :: Int }

addDepth :: DepthStats -> DepthStats
addDepth ds@DS {depth=depth} = ds {depth=depth + 1}

updateDS :: Bool -> DepthStats -> DepthStats
updateDS checkFeasibility (DS depth branches prunes) = DS (depth + 1) (branches + 1) (prunes + fromEnum checkFeasibility)
