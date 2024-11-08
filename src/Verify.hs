module Verify where

import GCLParser.Parser ( parseGCLfile )
import Utils.Type (Annotate, annotateWithTypes, programVars, TypedExpr (OpNeg))
import Tree.ProgramPath (extractPaths)
import Tree.Walk ( listPaths )
import Z3.Monad ( Z3, Result(..), evalZ3 )
import Predicate.Solver (assertPredicate)
import Tree.Wlp (feasibleWlp, validWlp)
import Simplifier.Simplifier (simplify)
import Config
import Tree.Data (Path, ControlPath, isExcept, getStmt, Step)
import Utils.Count (sizeOf)
import Stats (Stats(validSize))
import GCLParser.GCLDatatype (Program (..), VarDeclaration (VarDeclaration), Type (..), PrimitiveType (..))

type VarNames = ([String], [String], [String])
type Example = (Path, [(String, Maybe Integer)], [(String, Maybe Bool)], [(String, Maybe String)])

-- negate precondition, so that a result of "Unsat" indicates
-- that the formula is always true -> valid
getPrecond :: Bool -> [Step] -> TypedExpr
getPrecond False pth = OpNeg (validWlp pth)
getPrecond True pth  = simplify $ OpNeg (validWlp pth)

checkPath :: Bool -> VarNames -> Path -> Z3 ((Result, [Maybe Integer], [Maybe Bool], [Maybe String]), Int)
checkPath optF (intNames, boolNames, arrayNames) (pth, _) = do
  let precond = getPrecond optF pth
  (, sizeOf precond) <$> assertPredicate precond intNames boolNames arrayNames

checkPaths :: Bool -> VarNames -> [Path] -> Z3 (Maybe Example, Int)
checkPaths optF names@(intNames, boolNames, arrayNames) (stmt : stmts) = do
  ((result, intValues, boolValues, arrayValues), size) <- checkPath optF names stmt
  case result of
    Sat   -> return (Just (stmt, zip intNames intValues, zip boolNames boolValues, zip arrayNames arrayValues), size)
    Unsat -> do
      (res, totalSize) <- checkPaths optF names stmts
      return (res, size + totalSize)
    Undef -> error "Undef"
checkPaths _ _ [] = return (Nothing, 0)

annotateForProgram :: Program -> Annotate
annotateForProgram prgm = annotateWithTypes $ programVars prgm

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

stuff :: Config -> Program -> (VarNames, ControlPath)
stuff Config {depth=depth} prgm =
  (inputsOf prgm, extractPaths (annotateForProgram prgm) depth (stmt prgm))

findAssignment :: VarNames -> Path -> Z3 ((Result, [Maybe Integer], [Maybe Bool], [Maybe String]), Int)
findAssignment (intNames, boolNames, arrayNames) (pth, _) = do
  let precond = feasibleWlp (map getStmt pth)
  (, sizeOf precond) <$> assertPredicate precond intNames boolNames arrayNames

findFeasible :: VarNames -> [Path] -> Z3 (Maybe Example, Int)
findFeasible names@(intNames, boolNames, arrayNames) (pth : pths) = do
  ((result, intValues, boolValues, arrayValues), size) <- findAssignment names pth
  case result of
    Sat   -> return (Just (pth, zip intNames intValues, zip boolNames boolValues, zip arrayNames arrayValues), size)
    Unsat -> do
      (res, totalSize) <- findFeasible names pths
      return (res, size + totalSize)
    Undef -> error "Undef"
findFeasible _ [] = return (Nothing, 0)

checkTree :: Config -> Program -> Z3 (Maybe Example, Stats)
-- find exceptional paths
checkTree cfg@Config {heuristic=heuristic, optPruning=optB, optFormulas=optF, findExcept=True} prgm = do
  let (inputs, tree) = stuff cfg prgm
  (paths, stats) <- listPaths optF optB heuristic tree
  let exceptPaths = filter isExcept paths
  (res, validSize) <- findFeasible inputs exceptPaths
  return (res, stats { validSize = validSize })
-- check program validity
checkTree cfg@Config {heuristic=heuristic, optPruning=optB, optFormulas=optF, findExcept=False} prgm = do
  let (inputs, tree) = stuff cfg prgm
  (paths, stats) <- listPaths optF optB heuristic tree
  (res, validSize) <- checkPaths optF inputs paths
  return (res, stats { validSize = validSize })

checkProgram :: Config -> IO (Maybe Example, Stats)
checkProgram cfg@Config {file=filePath} = do
  gcl <- parseGCLfile filePath
  prgm <- case gcl of
    Left err -> error err
    Right prgm -> pure prgm
  evalZ3 $ checkTree cfg prgm
