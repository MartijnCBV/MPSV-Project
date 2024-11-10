module Main where

import Stats
import System.TimeIt
import Tree.Data (Step, Branch, BranchType (BExcept), Terminal (Except))
import Control.Monad (when)
import Verify
import Config (Config(..), config)
import Options.Applicative

printVals :: (a -> String) -> [(String, Maybe a)] -> IO ()
printVals _     []                        = pure ()
printVals toStr ((_, Nothing) : rest)     = printVals toStr rest
printVals toStr ((name, Just val) : rest) = do putStrLn $ concat [name, " = ", toStr val]; printVals toStr rest

printValues :: (Show a) => [(String, Maybe a)] -> IO ()
printValues = printVals show

printBranch :: Branch -> IO ()
printBranch (_, BExcept stmt, True)  = putStrLn $ stmt ++ " (exception)"
printBranch (_, BExcept stmt, False) = putStrLn $ stmt ++ " (no exception)"
printBranch (cond, btype, dir) = putStrLn $ concat [show btype, " ", show cond, " (", show dir, " branch)"]

printPath :: [Step] -> IO ()
printPath []                    = pure ()
printPath (Left stmt : rest)    = do print stmt; printPath rest
printPath (Right branch : rest) = do printBranch branch; printPath rest

printExample :: Bool -> Bool -> Example -> IO ()
printExample showPath findExcept ((path, term), intValues, boolValues, arrayValues) = do
  putStrLn $ getMsg FoundExample findExcept
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
printOut False time (Stats nodes unfins feasChecks infeasibles feasSize validSize) = do
  putStrLn $ concat ["Inspected ", show nodes, " nodes"]
  putStrLn $ concat ["Pruned ", show unfins, " incomplete paths and ", show infeasibles, " infeasible paths (checked ", show feasChecks, " times for feasibility)"]
  putStrLn $ concat ["Feasibility formulas size: ", show feasSize, "\nValidity formulas size: ", show validSize]
  putStrLn $ concat ["Took ", show time, " seconds"]
printOut True time (Stats nodes unfins feasChecks infeasibles feasSize validSize) =
  putStrLn $ concat [show time, ",", show validSize, ",", show nodes, ",", show unfins, ",", show feasChecks, ",", show infeasibles, ",", show feasSize]

data Msg = ProgramValid | FoundExample

getMsg :: Msg -> Bool -> String
getMsg ProgramValid False = "Program is valid"
getMsg ProgramValid True  = "No exceptional branch found"
getMsg FoundExample False = "Found counterexample for inputs:"
getMsg FoundExample True  = "Found exception for inputs:"

main :: IO ()
main = do
  cfg@Config {csv=csv, showPath=showPath, findExcept=findExcept} <- execParser opts
  (time, (result, stats)) <- timeItT $ checkProgram cfg
  printOut csv time stats
  case (csv, result) of
    (True, _) -> pure ()
    (_, Just err) -> printExample showPath findExcept err
    (_, Nothing) -> putStrLn $ getMsg ProgramValid findExcept
  return ()
  where
    opts = info (config <**> helper)
      ( fullDesc
     <> progDesc "Verify program described in FILE"
     <> header "Bounded Symbolic Verification" )
