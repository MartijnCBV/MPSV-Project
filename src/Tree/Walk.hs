module Tree.Walk where
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getFeasibleWlp)
import Tree.ProgramPath
import GCLParser.GCLDatatype
import Type (Annotate)
import Z3.Monad (Z3, Result (Sat, Unsat, Undef))
import Stats
import Control.Applicative
import Z3.Base (Tactic)

type Path = ([Stmt], Terminal)

-- simplest walk: list all complete paths
listPaths :: ControlPath -> [Path]
listPaths (Uni stmt next) = prependStmt stmt (listPaths next)
listPaths (Bin cond left right) =
  prependStmt (Assume cond) (listPaths left) ++ prependStmt (Assume (OpNeg cond)) (listPaths right)
listPaths (Leaf Unfin) = []
listPaths (Leaf term) = [([], term)]

prependStmt :: Stmt -> [Path] -> [Path]
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
walk :: Annotate -> (Stats -> Stats) -> [Stmt] -> Stmt -> ControlPath -> Maybe (Z3 Tactic) -> Z3 ([Path], Stats)
walk annotate updateStats prefix stmt next t = do
  (paths, stats) <- walkPaths annotate (stmt : prefix) next t
  return (prependStmt stmt paths, updateStats stats)

walkPaths :: Annotate -> [Stmt] -> ControlPath -> Maybe (Z3 Tactic) -> Z3 ([Path], Stats)
walkPaths _ _ (Leaf Unfin) _ = pure ([], unfin emptyStats)
walkPaths _ _ (Leaf term)  _ = pure ([([], term)], emptyStats)

walkPaths annotate prefix (Uni stmt next) t = walk annotate node prefix stmt next t
-- prune infeasible branches
walkPaths annotate prefix (Bin cond true false) t =
  feasible (getFeasibleWlp $ trueStmt : prefix) (\_ -> feasible (getFeasibleWlp $ falseStmt : prefix) branchTT branchTF t) branchFT t
  where feasible = isFeasible annotate
        trueStmt = Assume cond
        falseStmt = Assume (OpNeg $ Parens cond)
        branchFT _ = walk annotate (node . path . infeasible) prefix falseStmt false t
        branchTF _ = walk annotate (node . path . infeasible) prefix trueStmt true t
        branchTT _ = liftA2 mergePaths (walk annotate id prefix trueStmt true t) (walk annotate id prefix falseStmt false t)
        mergePaths (paths1, stats1) (paths2, stats2) = (paths1 ++ paths2, (node . path) stats1 +++ stats2)

isFeasible :: Annotate -> Expr -> (() -> Z3 ([Path], Stats)) -> (() -> Z3 ([Path], Stats))  -> Maybe (Z3 Tactic) -> Z3 ([Path], Stats)
isFeasible _        (LitB True) true _     _ = true ()
isFeasible annotate wlp         true false t = do
  (result, _, _, _) <- assertPredicate t (annotate wlp) [] [] []
  case result of
    Undef -> error "Undef"
    Unsat -> false ()
    Sat   -> true ()

pickPaths :: Annotate -> ControlPath -> Maybe (Z3 Tactic) -> Z3 ([Path], Stats)
pickPaths annotate = walkPaths annotate []
