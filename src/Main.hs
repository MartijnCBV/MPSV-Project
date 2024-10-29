{-# LANGUAGE InstanceSigs #-}
module Main where

import GCLParser.Parser ( parseGCLfile )
import Type (annotateForProgram, TypedExpr)
import Tree.ProgramPath (extractPaths)
import Tree.Walk (pickPaths)
import GCLParser.GCLDatatype
import Z3.Monad
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getWlp)
import Stats
import Traverse (traverseExpr)
import System.TimeIt
import Options.Applicative

type Path = Stmt
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

checkPath :: (Expr -> TypedExpr) -> ([String], [String], [String]) -> Stmt -> Z3 ((Result, [Maybe Integer], [Maybe Bool], [Maybe String]), Int)
checkPath annotate (intNames, boolNames, arrayNames) stmt = do
  -- negate precondition, so that a result of "Unsat" indicates
  -- that the formula is always true -> valid
  let precond = OpNeg (getWlp stmt)
  (, sizeOf precond) <$> assertPredicate (annotate precond) intNames boolNames arrayNames

checkPaths :: (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> Z3 (Either Example (), Int)
checkPaths annotate names@(intNames, boolNames, arrayNames) (stmt : stmts) = do
  ((result, intValues, boolValues, arrayValues), size) <- checkPath annotate names stmt
  case result of
    Sat   -> return (Left (stmt, zip intNames intValues, zip boolNames boolValues, zip arrayNames arrayValues), size)
    Unsat -> do
      (res, totalSize) <- checkPaths annotate names stmts
      return (res, size + totalSize)
    Undef -> error "Undef"
checkPaths _ _ [] = return (Right (), 0)

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

checkTree :: (Integral n) => n -> Program -> Z3 (Either Example (), Stats)
checkTree depth prgm = do
  let inputs = inputsOf prgm
  let annotate = annotateForProgram prgm
  let tree = extractPaths depth $ stmt prgm
  (paths, stats) <- pickPaths annotate tree
  (res, totalSize) <- checkPaths annotate inputs paths
  return (res, stats { totalSize = totalSize })

checkProgram :: Config -> IO (Either Example (), Stats)
checkProgram (Config filePath _ depth) = do
  gcl <- parseGCLfile filePath
  prgm <- case gcl of
    Left err -> error err
    Right prgm -> pure prgm
  evalZ3 $ checkTree depth prgm

data Config = Config {
  file :: String,
  csv :: Bool,
  depth :: Int
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

printValues :: (Show a) => [(String, Maybe a)] -> IO ()
printValues []                        = pure ()
printValues ((_, Nothing) : rest)     = printValues rest
printValues ((name, Just val) : rest) = do putStrLn $ concat [name, " = ", show val]; printValues rest

printExample :: Example -> IO ()
printExample (_, intValues, boolValues, arrayValues) = do
  putStrLn "Found counterexample for inputs:"
  printValues intValues
  printValues boolValues
  printValues arrayValues
  return ()

printOut :: Bool -> Double -> Stats -> IO ()
printOut False time (Stats nodes paths unfins infeasibles size) = do
  putStrLn $ concat ["Inspected ", show nodes, " nodes in ", show paths, " paths"]
  putStrLn $ concat ["Pruned ", show unfins, " incomplete paths and ", show infeasibles, " infeasible paths"]
  putStrLn $ concat ["Verified formulas with total size of ", show size, "\nTook ", show time, " seconds"]
printOut True time (Stats nodes paths unfins infeasibles size) =
  putStrLn $ concat [show time, ",", show size, ",", show nodes, ",", show paths, ",", show unfins, ",", show infeasibles]

main :: IO ()
main = do
  cfg <- execParser opts
  (time, (result, stats)) <- timeItT $ checkProgram cfg
  let printCsv = csv cfg
  printOut printCsv time stats
  case (printCsv, result) of
    (True, _) -> pure ()
    (_, Left err) -> printExample err
    (_, Right ()) -> putStrLn "Program is valid"
  return ()
  where
    opts = info (config <**> helper)
      ( fullDesc
     <> progDesc "Verify program described in FILE"
     <> header "Bounded Symbolic Verification" )
