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
  (paths, stats) <- pickPaths annotate tree-- `debug` show tree
  (res, totalSize) <- checkPaths annotate inputs paths
  return (res, stats { totalSize = totalSize })

checkProgram :: (Integral n) => n -> String -> IO (Either Example (), Stats)
checkProgram depth filePath = do
  gcl <- parseGCLfile filePath
  prgm <- case gcl of
    Left err -> error err
    Right prgm -> pure prgm
  evalZ3 $ checkTree depth prgm

main :: IO ()
main = putStrLn "Hello world"
