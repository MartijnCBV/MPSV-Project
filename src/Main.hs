module Main where

import GCLParser.Parser ( parseGCLfile )
import Type (annotateForProgram, TypedExpr)
import Tree.ProgramPath (extractPaths, listPaths)
import GCLParser.GCLDatatype
import Z3.Monad
import Predicate.Solver (assertPredicates)
import Tree.Wlp (getWlp)
import Control.Concurrent
import Data.Time.Clock
import Z3.Monad (Z3Env)

type Path = Stmt
type Example = (Path, [(String, Maybe Integer)], [(String, Maybe Bool)], [(String, Maybe String)])

threaded :: Bool
threaded = False
numOfThreads :: Int
numOfThreads = 8
wlpInBulk :: Bool
wlpInBulk = not threaded 

negateWlp :: (Expr -> TypedExpr) -> Stmt -> TypedExpr
-- negate precondition, so that a result of "Unsat" indicates
-- that the formula is always true -> valid
negateWlp annotate stmt = annotate (OpNeg (getWlp stmt))

checkPaths :: Bool -> (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> IO (Either Example ())
checkPaths True = checkPathsInBulk
checkPaths False = checkPathsPerOne

checkPathsInBulk :: (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> IO (Either Example ())
checkPathsInBulk annotate names@(intNames, boolNames, arrayNames) stmts = do  
  (result, intValues, boolValues, arrayValues, stmt) <- evalZ3 (assertPredicates negatedWlps intNames boolNames arrayNames)
  case result of
    Sat   -> return $ Left (stmt, zip intNames intValues, zip boolNames boolValues, zip arrayNames arrayValues)
    Unsat -> return $ Right ()
    Undef -> error "Undef"
  where
    negatedWlps = zip (map (negateWlp annotate) stmts) stmts

checkPathsPerOne :: (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> IO (Either Example ())
checkPathsPerOne _        _                                       []           = return $ Right ()  
checkPathsPerOne annotate names@(intNames, boolNames, arrayNames) (stmt:stmts) = do  
  result <- checkPathsInBulk annotate names [stmt]
  case result of
    Right _ -> checkPathsPerOne annotate names stmts
    Left _   -> return result
 

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

checkProgram :: (Integral n) => n -> String -> IO ([Either Example ()])
checkProgram depth path = do
  gcl <- parseGCLfile path
  prgm <- case gcl of
    Left err -> error err
    Right prgm -> pure prgm
  let annotate = annotateForProgram prgm
  let inputs = inputsOf prgm
  let paths = listPaths $ extractPaths depth (stmt prgm)
  if threaded 
    then do
      checkPathsParallel numOfThreads annotate inputs paths
    else do
      result <- checkPaths wlpInBulk annotate inputs paths
      return [result]

checkPathsParallel :: Int -> (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> IO ([Either Example ()])
checkPathsParallel threads annote params paths = _checkPathsParallel threads (((length paths) `div` threads) + 1) [] annote params paths 
  
_checkPathsParallel :: Int -> Int -> [MVar (Either Example ())] -> (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> IO ([Either Example ()])
_checkPathsParallel 0 _ results _ _ _ = mapM readMVar results -- TODO kill other threads if one thread returns invalid
_checkPathsParallel _ _ results _ _ [] = mapM readMVar results
_checkPathsParallel threads maxPaths results annotate params paths = do
  out <- newEmptyMVar
  (myPaths, rest) <- return $ splitAt maxPaths paths
  threadId <-  forkIO (threadCheckPaths out annotate params myPaths)
  _checkPathsParallel (threads-1) maxPaths (out:results) annotate params rest

threadCheckPaths :: MVar (Either Example ()) -> (Expr -> TypedExpr) -> ([String], [String], [String]) -> [Stmt] -> IO ()
threadCheckPaths outVar annotate params paths = do
  result <- checkPaths wlpInBulk annotate params paths
  putStrLn (show (length paths))
  putMVar outVar result


main :: IO ()
main = do  
  maxThreads <- getNumCapabilities
  putStrLn $ "Threaded: " ++ (show threaded) ++ " Threads: " ++ (show numOfThreads) ++ "/" ++ (show maxThreads) ++ " wlpInBulk: " ++ (show wlpInBulk)
  putStrLn . show =<< getCurrentTime
  result <- checkProgram 30 "./examples/benchmark/memberOf.gcl"
  putStrLn $ show result
  putStrLn . show =<< getCurrentTime
