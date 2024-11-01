{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
module Main where

import GCLParser.Parser ( parseGCLfile )
import Type (annotateForProgram, TypedExpr)
import Tree.ProgramPath (extractPaths)
import Tree.Walk
import GCLParser.GCLDatatype
import Z3.Monad
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getWlp)
import Stats
import Traverse (traverseExpr)
import System.TimeIt
import Options.Applicative
import Tree.Data (Path, Step, Branch, BranchType (BExcept), Terminal (Except))
import Control.Monad (when)
import Tree.Heuristic
    ( HeuristicMeasure(Depth),
      Heuristic,
      never,
      checkAll,
      linear,
      exponential,
      untilDepth )

type Example = (Path, [(String, Maybe Integer)], [(String, Maybe Bool)], [(String, Maybe String)])

newtype SemigroupInt = SemigroupInt Int

toInt :: SemigroupInt -> Int
toInt (SemigroupInt i) = i

instance Semigroup SemigroupInt where
  (<>) :: SemigroupInt -> SemigroupInt -> SemigroupInt
  (SemigroupInt i1) <> (SemigroupInt i2) = SemigroupInt $ i1 + i2

sizeOf :: Expr -> Int
sizeOf = toInt . traverseExpr (SemigroupInt . isLeaf)
         where isLeaf (Var _)  = 1
               isLeaf (LitB _) = 1
               isLeaf (LitI _) = 1
               isLeaf _        = 0

checkPath :: (Expr -> TypedExpr) -> ([String], [String], [String]) -> Path -> Z3 ((Result, [Maybe Integer], [Maybe Bool], [Maybe String]), Int)
checkPath annotate (intNames, boolNames, arrayNames) (pth, _) = do
  -- negate precondition, so that a result of "Unsat" indicates
  -- that the formula is always true -> valid
  let precond = OpNeg (getWlp pth)
  (, sizeOf precond) <$> assertPredicate (annotate precond) intNames boolNames arrayNames

checkPaths :: (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Path] -> Z3 (Maybe Example, Int)
checkPaths annotate names@(intNames, boolNames, arrayNames) (stmt : stmts) = do
  ((result, intValues, boolValues, arrayValues), size) <- checkPath annotate names stmt
  case result of
    Sat   -> return (Just (stmt, zip intNames intValues, zip boolNames boolValues, zip arrayNames arrayValues), size)
    Unsat -> do
      (res, totalSize) <- checkPaths annotate names stmts
      return (res, size + totalSize)
    Undef -> error "Undef"
checkPaths _ _ [] = return (Nothing, 0)

inputsOf :: Program -> ([String], [String], [String])
inputsOf prgm = (map getName (filter isInt inputs), map getName (filter isBool inputs), map getName (filter isArray inputs))
  where inputs = input prgm
        isInt varDecl = case varDecl of
          VarDeclaration _ (PType PTInt) -> True
          _ -> False
        isBool varDecl = case varDecl of
          VarDeclaration _ (PType PTBool) -> True
          _ -> False
        isArray varDecl = case varDecl of
          VarDeclaration _ (AType PTInt) -> True
          _ -> False
        getName (VarDeclaration name _) = name

checkTree :: Config -> Program -> Z3 (Maybe Example, Stats)
checkTree Config {depth=depth, heuristic=heuristic, optPruning=optPruning} prgm = do
  let inputs = inputsOf prgm
  let annotate = annotateForProgram prgm
  let tree = extractPaths depth $ stmt prgm
  (paths, stats) <- listPaths optPruning heuristic annotate tree
  (res, totalSize) <- checkPaths annotate inputs paths
  return (res, stats { totalSize = totalSize })

checkProgram :: Config -> IO (Maybe Example, Stats)
checkProgram cfg@Config {file=filePath} = do
  gcl <- parseGCLfile filePath
  prgm <- case gcl of
    Left err -> error err
    Right prgm -> pure prgm
  evalZ3 $ checkTree cfg prgm

data Config = Config {
  file :: String,
  depth :: Int,
  heuristic :: Heuristic,
  optPruning :: Bool,
  csv :: Bool,
  showPath :: Bool
}

parseHeuristic :: ReadM (Int -> Heuristic)
parseHeuristic = eitherReader $ \case
  "never"     -> Right $ const never
  "always"    -> Right $ const checkAll
  "second"    -> Right $ \_ -> linear 2 Depth
  "expSecond" -> Right $ \_ -> exponential 2 Depth
  "half"      -> Right $ \d -> untilDepth (d `div` 2) Depth checkAll
  s           -> Left $ "Unsupported heuristic: " ++ s

mkConfig :: String -> Int -> (Int -> Heuristic) -> Bool -> Bool -> Bool -> Config
mkConfig f d mkH = Config f d (mkH d)

config :: Parser Config
config = mkConfig
      <$> argument str
          ( metavar "FILE"
         <> help "File to verify" )
      <*> option auto
          ( long "depth"
         <> short 'd'
         <> help "Depth to verify to"
         <> showDefault
         <> value 10
         <> metavar "INT" )
      <*> option parseHeuristic
          ( long "heur"
         <> short 'h'
         <> help "Branch pruning heuristic to use"
         <> value (const checkAll)
         <> metavar "NAME")
      <*> switch
          ( long "opt"
         <> short 'o'
         <> help "Optimize branch pruning")
      <*> switch
          ( long "csv"
         <> help "Print in CSV format")
      <*> switch
          ( long "path"
         <> short 'p'
         <> help "Show counterexample's path")

printVals :: (a -> String) -> [(String, Maybe a)] -> IO ()
printVals _     []                        = pure ()
printVals toStr ((_, Nothing) : rest)     = printVals toStr rest
printVals toStr ((name, Just val) : rest) = do putStrLn $ concat [name, " = ", toStr val]; printVals toStr rest

printValues :: (Show a) => [(String, Maybe a)] -> IO ()
printValues = printVals show

printBranch :: Branch -> IO ()
printBranch (_, BExcept stmt, True)  = putStrLn $ "Exception in: " ++ stmt
printBranch (_, BExcept stmt, False) = putStrLn $ "No exception in: " ++ stmt
printBranch (cond, btype, dir) = putStrLn $ concat ["Branch ", show dir, " in ", show btype, " ", show cond]

printPath :: [Step] -> IO ()
printPath []                    = pure ()
printPath (Left stmt : rest)    = do print stmt; printPath rest
printPath (Right branch : rest) = do printBranch branch; printPath rest

printExample :: Bool -> Example -> IO ()
printExample showPath ((path, term), intValues, boolValues, arrayValues) = do
  putStrLn "Found counterexample for inputs:"
  printValues intValues
  printValues boolValues
  printVals id arrayValues
  when showPath doShowPath
  where doShowPath = do
                    putStrLn "Path:"
                    printPath path
                    case term of
                      Except -> putStrLn "Terminating exceptionally"
                      _      -> putStrLn "Terminating normally"
                    return ()

printOut :: Bool -> Double -> Stats -> IO ()
printOut False time (Stats nodes unfins infeasibles size) = do
  putStrLn $ concat ["Inspected ", show nodes, " nodes"]
  putStrLn $ concat ["Pruned ", show unfins, " incomplete paths and ", show infeasibles, " infeasible paths"]
  putStrLn $ concat ["Verified formulas with total size of ", show size, "\nTook ", show time, " seconds"]
printOut True time (Stats nodes unfins infeasibles size) =
  putStrLn $ concat [show time, ",", show size, ",", show nodes, ",", show unfins, ",", show infeasibles]

main :: IO ()
main = do
  cfg@Config {csv=csv, showPath=showPath} <- execParser opts
  (time, (result, stats)) <- timeItT $ checkProgram cfg
  printOut csv time stats
  case (csv, result) of
    (True, _) -> pure ()
    (_, Just err) -> printExample showPath err
    (_, Nothing) -> putStrLn "Program is valid"
  return ()
  where
    opts = info (config <**> helper)
      ( fullDesc
     <> progDesc "Verify program described in FILE"
     <> header "Bounded Symbolic Verification" )
