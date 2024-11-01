{-# LANGUAGE InstanceSigs #-}
module Main where

import GCLParser.Parser ( parseGCLfile )
import Type (annotateForProgram, TypedExpr)
import Tree.ProgramPath (extractPaths)
import Tree.Walk (pickPaths, Path)
import GCLParser.GCLDatatype
import Z3.Monad
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getWlp)
import Stats
import Traverse (traverseExpr)
import System.TimeIt
import Options.Applicative
import Data.List (intercalate)
import Z3.Base (Tactic)
import Predicate.Tactics

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

checkPath :: (Expr -> TypedExpr) -> ([String], [String], [String]) -> Path -> Maybe (Z3 Tactic) -> Z3 ((Result, [Maybe Integer], [Maybe Bool], [Maybe String]), Int)
checkPath annotate (intNames, boolNames, arrayNames) (pth, _) t = do
  -- negate precondition, so that a result of "Unsat" indicates
  -- that the formula is always true -> valid
  let precond = OpNeg (getWlp pth)
  (, sizeOf precond) <$> assertPredicate t (annotate precond) intNames boolNames arrayNames

checkPaths :: (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Path] -> Maybe (Z3 Tactic) -> Z3 (Either Example (), Int)
checkPaths annotate names@(intNames, boolNames, arrayNames) (stmt : stmts) t = do
  ((result, intValues, boolValues, arrayValues), size) <- checkPath annotate names stmt t
  case result of
    Sat   -> return (Left (stmt, zip intNames intValues, zip boolNames boolValues, zip arrayNames arrayValues), size)
    Unsat -> do
      (res, totalSize) <- checkPaths annotate names stmts t
      return (res, size + totalSize)
    Undef -> error "Undef"
checkPaths _ _ [] _ = return (Right (), 0)

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

checkTree :: (Integral n) => n -> Program -> Maybe (Z3 Tactic) -> Z3 (Either Example (), Stats)
checkTree depth prgm t = do
  let inputs = inputsOf prgm
  let annotate = annotateForProgram prgm
  let tree = extractPaths depth $ stmt prgm
  (paths, stats) <- pickPaths annotate tree t
  (res, totalSize) <- checkPaths annotate inputs paths t
  return (res, stats { totalSize = totalSize })

checkProgram :: Int -> String -> Maybe (Z3 Tactic) -> IO (Either Example (), Stats)
checkProgram depth filePath t = do
  gcl <- parseGCLfile filePath
  prgm <- case gcl of
    Left err -> error err
    Right prgm -> pure prgm
  evalZ3 $ checkTree depth prgm t

data Config = Config {
  file :: String,
  csv :: Bool,
  depth :: Int,
  runs :: Int
}

config :: Parser Config
config = Config
      <$> argument str
          ( metavar "FILE"
         <> help "File to verify" )
      <*> switch
          ( long "csv"
         <> help "Print in CSV format")
      <*> option auto
          ( long "depth"
         <> short 'd'
         <> help "Depth to verify to"
         <> showDefault
         <> value 10
         <> metavar "INT" )
      <*> option auto
          ( long "runs"
         <> short 'r'
         <> help "Amount of runs to perform"
         <> showDefault
         <> value 1
         <> metavar "INT" )

printVals :: (a -> String) -> [(String, Maybe a)] -> IO ()
printVals _     []                        = pure ()
printVals toStr ((_, Nothing) : rest)     = printVals toStr rest
printVals toStr ((name, Just val) : rest) = do putStrLn $ concat [name, " = ", toStr val]; printVals toStr rest

printValues :: (Show a) => [(String, Maybe a)] -> IO ()
printValues = printVals show

printExample :: Example -> IO ()
printExample (_, intValues, boolValues, arrayValues) = do
  putStrLn "Found counterexample for inputs:"
  printValues intValues
  printValues boolValues
  printVals id arrayValues
  return ()

printOut :: Bool -> Double -> Stats -> IO ()
printOut False time (Stats nodes paths unfins infeasibles size) = do
  putStrLn $ concat ["Inspected ", show nodes, " nodes in ", show paths, " paths"]
  putStrLn $ concat ["Pruned ", show unfins, " incomplete paths and ", show infeasibles, " infeasible paths"]
  putStrLn $ concat ["Verified formulas with total size of ", show size, "\nTook ", show time, " seconds"]
printOut True time (Stats nodes paths unfins infeasibles size) =
  putStrLn $ concat [show time, ",", show size, ",", show nodes, ",", show paths, ",", show unfins, ",", show infeasibles]

execHandleRes :: Bool -> Either Example () -> IO ()
execHandleRes csv result = case (csv, result) of
    (True, _) -> pure ()
    (_, Left err) -> printExample err
    (_, Right ()) -> putStrLn "Program is valid"

exec' :: String -> Bool -> Int -> Int -> [Double] -> Maybe (Z3 Tactic) -> IO ()
exec' filePath csv depth 1 pts t = do
  (time, (result, stats)) <- timeItT $ checkProgram depth filePath t
  -- printOut csv time stats
  -- execHandleRes csv result
  putStrLn "All run times:"
  putStrLn $ intercalate "," $ map show (time:pts)
  let avg  = sum (time:pts) / fromIntegral (length (time:pts))
      high = maximum (time:pts)
      low  = minimum (time:pts)
  putStrLn $ concat ["Average: ", show avg, " Best: ", show low," Worst: ", show high,  " Variance: ", show $ high - low]
exec' filePath csv depth n pts t = do
  (time, (result, stats)) <- timeItT $ checkProgram depth filePath t
  -- printOut csv time stats
  -- execHandleRes csv result
  exec' filePath csv depth (n-1) (time:pts) t

exec :: IO ()
exec = do
  (Config filePath csv depth runs) <- execParser opts
  exec' filePath csv depth 10   [] Nothing
  exec' filePath csv depth runs [] Nothing
  exec' filePath csv depth 10   [] $ Just chain
  exec' filePath csv depth runs [] $ Just chain
  where
    opts = info (config <**> helper)
      ( fullDesc
     <> progDesc "Verify program described in FILE"
     <> header "Bounded Symbolic Verification" )


main :: IO ()
main = exec
