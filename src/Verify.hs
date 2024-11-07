{-# LANGUAGE InstanceSigs #-}
module Verify where

import GCLParser.Parser ( parseGCLfile )
import Type (Annotate, annotateWithTypes, programVars)
import Tree.ProgramPath (extractPaths)
import Tree.Walk
import GCLParser.GCLDatatype
import Z3.Monad ( Z3, Result(..), evalZ3 )
import Predicate.Solver (assertPredicate)
import Tree.Wlp (feasibleWlp, validWlp)
import Stats
import Traverse (traverseExpr)
import Simplifier.Simplifier (simplify)
import Config
import Tree.Data (Path, ControlPath, isExcept, getStmt)

type VarNames = ([String], [String], [String])
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

checkPath :: Annotate -> VarNames -> Path -> Z3 ((Result, [Maybe Integer], [Maybe Bool], [Maybe String]), Int)
checkPath annotate (intNames, boolNames, arrayNames) (pth, _) = do
  -- negate precondition, so that a result of "Unsat" indicates
  -- that the formula is always true -> valid
  let precond = OpNeg (validWlp pth)
  (, sizeOf precond) <$> assertPredicate (annotate precond) intNames boolNames arrayNames

checkPaths :: Annotate -> VarNames -> [Path] -> Z3 (Maybe Example, Int)
checkPaths annotate names@(intNames, boolNames, arrayNames) (stmt : stmts) = do
  ((result, intValues, boolValues, arrayValues), size) <- checkPath annotate names stmt
  case result of
    Sat   -> return (Just (stmt, zip intNames intValues, zip boolNames boolValues, zip arrayNames arrayValues), size)
    Unsat -> do
      (res, totalSize) <- checkPaths annotate names stmts
      return (res, size + totalSize)
    Undef -> error "Undef"
checkPaths _ _ [] = return (Nothing, 0)

annotateForProgram :: Bool -> Program -> Annotate
annotateForProgram False prgm = annotateWithTypes $ programVars prgm
annotateForProgram True prgm  = simplify . annotateWithTypes (programVars prgm)

inputsOf :: Program -> VarNames
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

stuff :: Config -> Program -> (VarNames, Annotate, ControlPath)
stuff Config {optFormulas=optFormulas, depth=depth} prgm =
  (inputsOf prgm, annotateForProgram optFormulas prgm, extractPaths depth $ stmt prgm)

findAssignment :: Annotate -> VarNames -> Path -> Z3 ((Result, [Maybe Integer], [Maybe Bool], [Maybe String]), Int)
findAssignment annotate (intNames, boolNames, arrayNames) (pth, _) = do
  let precond = feasibleWlp (map getStmt pth)
  (, sizeOf precond) <$> assertPredicate (annotate precond) intNames boolNames arrayNames

findFeasible :: Annotate -> VarNames -> [Path] -> Z3 (Maybe Example, Int)
findFeasible annotate names@(intNames, boolNames, arrayNames) (pth : pths) = do
  ((result, intValues, boolValues, arrayValues), size) <- findAssignment annotate names pth
  case result of
    Sat   -> return (Just (pth, zip intNames intValues, zip boolNames boolValues, zip arrayNames arrayValues), size)
    Unsat -> do
      (res, totalSize) <- findFeasible annotate names pths
      return (res, size + totalSize)
    Undef -> error "Undef"
findFeasible _ _ [] = return (Nothing, 0)

checkTree :: Config -> Program -> Z3 (Maybe Example, Stats)
-- find exceptional paths
checkTree cfg@Config {heuristic=heuristic, optPruning=optPruning, findExcept=True} prgm = do
  let (inputs, annotate, tree) = stuff cfg prgm
  (paths, stats) <- listPaths optPruning heuristic annotate tree
  let exceptPaths = filter isExcept paths
  (res, totalSize) <- findFeasible annotate inputs exceptPaths
  return (res, stats { totalSize = totalSize })
-- check program validity
checkTree cfg@Config {heuristic=heuristic, optPruning=optPruning, findExcept=False} prgm = do
  let (inputs, annotate, tree) = stuff cfg prgm
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
