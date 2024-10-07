module Main where

import GCLParser.Parser ( parseGCLfile )
import Type (annotateForProgram, TypedExpr)
import Tree.ProgramPath (extractPaths, listPaths)
import GCLParser.GCLDatatype
import Z3.Monad
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getWlp)

type Path = Stmt
type Example = (Path, [(String, Maybe Integer)], [(String, Maybe Bool)])

checkPath :: (Expr -> TypedExpr) -> ([String], [String]) -> Stmt -> IO (Result, [Maybe Integer], [Maybe Bool])
checkPath annotate (intNames, boolNames) stmt = do
  -- negate precondition, so that a result of "Unsat" indicates
  -- that the formula is always true -> valid
  let precond = OpNeg (getWlp stmt)
  evalZ3 (assertPredicate (annotate precond) intNames boolNames)

checkPaths :: (Expr -> TypedExpr) -> ([String], [String]) -> [Stmt] -> IO (Either Example ())
checkPaths annotate names@(intNames, boolNames) (stmt : stmts) = do
  (result, intValues, boolValues) <- checkPath annotate names stmt
  case result of
    Sat   -> return $ Left (stmt, zip intNames intValues, zip boolNames boolValues)
    Unsat -> checkPaths annotate names stmts
    Undef -> error "Undef"
checkPaths _ _ [] = return $ Right ()

inputsOf :: Program -> ([String], [String])
inputsOf prgm = (map getName (filter isInt inputs), map getName (filter isBool inputs))
  where inputs = input prgm
        isInt varDecl = case varDecl of
          VarDeclaration _ (PType PTInt) -> True
          _ -> False
        isBool varDecl = case varDecl of
          VarDeclaration _ (PType PTBool) -> True
          _ -> False
        getName (VarDeclaration name _) = name

checkProgram :: (Integral n) => n -> String -> IO (Either Example ())
checkProgram depth path = do
  gcl <- parseGCLfile path
  prgm <- case gcl of
    Left err -> error err
    Right prgm -> pure prgm
  let inputs = inputsOf prgm
  let paths = listPaths $ extractPaths depth (stmt prgm)
  checkPaths (annotateForProgram prgm) inputs paths

main :: IO ()
main = putStrLn "Hello world"
