# Verification and Proof Engine (VAPE) user manual

Provide VAPE with the name of the file containing the program you want to verify. Additional options can be provided as follows:

- `--depth INT` or `-d INT`: the K-parameter the maximum depth to which to verify the program. Default value 10.
- `--path` or `-p`: when finding a counterexample, show the counterexample's path through the program.
- `--find-except` or `-e`: search for feasible program paths that terminate exceptionally instead of verifying program validity.
- `--heuristic NAME` or `-h NAME`: branch pruning heuristic strategy to use. Default value `always`. See heuristics section for more details on options.
- `--opt-branch`: turn on optimized branch pruning. Causes the engine to assume the other branch is feasible when finding an infeasible branch.
- `--opt-valid`: simplify formulas for checking validity of paths.
- `--opt-feasible`: simplify formulas for checking feasibility of paths.
- `--csv`: print output statistics in CSV format.

An example command using `cabal run` would be `cabal run exes -- benchmark/memberOf.gcl -d 50 --opt-branches -p`. The output should look similar to the following:
```
Inspected 147 nodes
Pruned 0 incomplete paths and 35 infeasible paths (checked 60 times for feasibility)
Feasibility formulas size: 5022
Validity formulas size: 97
Took 0.465492911 seconds
Found counterexample for inputs:
x = 6
a = [6,6,6,6]
Path:
assume (((#(a)<=4)/\(#(a)>=0))/\(E "i"((((0<=i)/\(i<#(a)))/\(a[i]=x)))))
k := 0
found := False
while (k<#(a)) (True branch)
if (a[k]=x) (no exception)
if (a[k]=x) (True branch)
found := True
k := (k+1)
while (k<#(a)) (True branch)
if (a[k]=x) (no exception)
if (a[k]=x) (True branch)
found := True
k := (k+1)
while (k<#(a)) (True branch)
if (a[k]=x) (no exception)
if (a[k]=x) (True branch)
found := True
k := (k+1)
while (k<#(a)) (True branch)
if (a[k]=x) (no exception)
if (a[k]=x) (True branch)
found := True
k := (k+1)
while (k<#(a)) (False branch)
assert (((~found/\(k>=0))/\(k=#(a)))/\(k<=4))
Terminating normally
```

## Heuristics
VAPE admits a large number of different heuristic strategies to use for determining when to check branches for feasibility.

Some heuristic strategies mention a depth measure: depth in the execution tree can be measured in many different ways, but VAPE admits to different ways to measure depth. Node depth is the number of nodes that occur before the branch in the current execution path. Branch depth is the number of branches that occur before the branch in the current execution path. For instance, in the following GCL program:
```
min(x:int, y:int | z:int) {
  z := x ;
  if y < x then { z := y } else { skip } ;
  assert ((z = x) || (z = y)) && (z <= x) && (z <= y)
}
```
The `assert` statement is at a node depth of 3, since there are three nodes before it in the path: (1) the assignment on the first line, (2) the if statement, and (3) the then or else clause of the if statement. It is at a branch depth of 1, since there is only the if-branch before it.


- `never`: Never check for branch feasibility.
- `always`: Always check for branch feasibility.
- `alwaysHalf`: Always check for feasibility until a node depth of half of K is reached.
- `alwaysHalfB`: As `alwaysHalf`, but using branch depth.
- `linN`: Check every time the node depth is a multiple of N. For instance, `lin2` would check a branch if its node depth is 0, 2, 4, 6, ...
- `linBN`: As `linN`, but using branch depth.
- `expN`: Check every time the node depth is a power of N. For instance, `exp2` would check a branch if its node depth is 1, 2, 4, 8, ...
- `expBN`: As `expN`, but using branch depth.
- `expHalf`: As `alwaysHalf`, but instead of stopping after the node depth is half of K, it switches to `exp2`.
- `expHalfB`: As `alwaysHalfB`, but switches to `exp2` instead of stopping.
- `linHalf`: Use `linB2` until a node depth is half of K is reached, and then switch to `exp2`.
- `linHalfB`: As `linHalf`, but switches after a branch depth of half of K is reached.
- `thirds`: As `always` while the node depth is below a third of K, then as `linB2` while the node depth is below two-thirds of K, then finally as `exp2`.
- `thirdsB`: As `thirds`, but using the branch depth instead.
- `minConjN`: Check only if the feasibility formula contains at least N conjunctions.
- `minSizeN`: Check only if the feasibility formula contains at least N atoms.
- `maxSizeN`: Check only if the feasibility formula contains at most N atoms.
