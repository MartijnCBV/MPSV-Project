module Main where

import GCLParser.Parser ( parseGCLfile )
import Type (annotateForProgram, TypedExpr)
import Tree.ProgramPath (extractPaths, listPaths)
import GCLParser.GCLDatatype
import Z3.Monad
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getWlp)
import Control.Parallel
import Control.Concurrent
import Data.Time.Clock

type Path = Stmt
type Example = (Path, [(String, Maybe Integer)], [(String, Maybe Bool)], [(String, Maybe String)])

checkPath :: (Expr -> TypedExpr) -> ([String], [String], [String]) -> Stmt -> IO (Result, [Maybe Integer], [Maybe Bool], [Maybe String])
checkPath annotate (intNames, boolNames, arrayNames) stmt = do
  -- negate precondition, so that a result of "Unsat" indicates
  -- that the formula is always true -> valid
  let precond = OpNeg (getWlp stmt)
  evalZ3 (assertPredicate (annotate precond) intNames boolNames arrayNames)

checkPaths :: (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> IO (Either Example ())
checkPaths annotate names@(intNames, boolNames, arrayNames) (stmt : stmts) = do
  -- (result, intValues, boolValues, arrayValues) <- rest `par` (checkPath annotate names stmt)
  (result, intValues, boolValues, arrayValues) <- checkPath annotate names stmt
  case result of
    Sat   -> return $ Left (stmt, zip intNames intValues, zip boolNames boolValues, zip arrayNames arrayValues)
    Unsat -> rest
    Undef -> error "Undef"
  where
    rest = checkPaths annotate names stmts
checkPaths _ _ [] = return $ Right ()

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

checkProgram :: (Integral n) => n -> Int -> String -> IO ([Either Example ()])
checkProgram depth threads path = do
  gcl <- parseGCLfile path
  prgm <- case gcl of
    Left err -> error err
    Right prgm -> pure prgm
  let inputs = inputsOf prgm
  let paths = listPaths $ extractPaths depth (stmt prgm)
  checkPathsParallel threads (annotateForProgram prgm) inputs paths

checkPathsParallel :: Int -> (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> IO ([Either Example ()])
checkPathsParallel threads annote params paths = _checkPathsParallel threads (((length paths) `div` threads) + 1) [] annote params paths 
  
_checkPathsParallel :: Int -> Int -> [MVar (Either Example ())] -> (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> IO ([Either Example ()])
_checkPathsParallel 0 _ results _ _ _ = mapM readMVar results
_checkPathsParallel _ _ results _ _ [] = mapM readMVar results
_checkPathsParallel threads maxPaths results annotate params paths = do
  out <- newEmptyMVar
  (myPaths, rest) <- return $ splitAt maxPaths paths
  threadId <- forkIO (threadCheckPaths out annotate params myPaths)
  _checkPathsParallel (threads-1) maxPaths (out:results) annotate params rest

threadCheckPaths :: MVar (Either Example ()) -> (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> IO ()
threadCheckPaths outVar annotate params paths = do
  result <- checkPaths annotate params paths
  putMVar outVar result


main :: IO ()
main = do
  putStrLn "Threads: 8"
  begin <- getCurrentTime
  result <- checkProgram 37 8 "./examples/benchmark/memberOf.gcl"
  end <- getCurrentTime
  putStrLn (show (begin))
  putStrLn (show (end))
  putStrLn $ show result
  
  putStrLn "Threads: 1"
  begin <- getCurrentTime
  result <- checkProgram 37 1 "./examples/benchmark/memberOf.gcl"
  end <- getCurrentTime
  putStrLn (show (begin))
  putStrLn (show (end))
  putStrLn $ show result
  
  putStrLn "Threads: 2"
  begin <- getCurrentTime
  result <- checkProgram 37 2 "./examples/benchmark/memberOf.gcl"
  end <- getCurrentTime
  putStrLn (show (begin))
  putStrLn (show (end))
  putStrLn $ show result
  
  putStrLn "Threads: 4"
  begin <- getCurrentTime
  result <- checkProgram 37 4 "./examples/benchmark/memberOf.gcl"
  end <- getCurrentTime
  putStrLn (show (begin))
  putStrLn (show (end))
  putStrLn $ show result
  
  putStrLn "Threads: 8"
  begin <- getCurrentTime
  result <- checkProgram 37 8 "./examples/benchmark/memberOf.gcl"
  end <- getCurrentTime
  putStrLn (show (begin))
  putStrLn (show (end))
  putStrLn $ show result
  
  putStrLn "Threads: 16"
  begin <- getCurrentTime
  result <- checkProgram 37 16 "./examples/benchmark/memberOf.gcl"
  end <- getCurrentTime
  putStrLn (show (begin))
  putStrLn (show (end))
  putStrLn $ show result
  
  putStrLn "Threads: 32"
  begin <- getCurrentTime
  result <- checkProgram 37 32 "./examples/benchmark/memberOf.gcl"
  end <- getCurrentTime
  putStrLn (show (begin))
  putStrLn (show (end))
  putStrLn $ show result
  
