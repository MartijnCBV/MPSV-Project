module Main where

import GCLParser.Parser ( parseGCLfile )
import Type (annotateForProgram, TypedExpr)
import Tree.ProgramPath (extractPaths, listPaths)
import GCLParser.GCLDatatype
import Z3.Monad
import Predicate.Solver (assertPredicate)
import Tree.Wlp (getWlp)

checkPath :: (Expr -> TypedExpr) -> Stmt -> IO (Result, [Maybe Integer], [Maybe Bool])
checkPath annotate stmt = do
  -- negate precondition, so that a result of "Unsat" indicates
  -- that the formula is always true -> valid
  let precond = OpNeg (getWlp stmt)
  evalZ3 (assertPredicate (annotate precond) [] [])

checkPaths :: (Expr -> TypedExpr) -> [Stmt] -> IO (Either () ())
checkPaths annotate (stmt : stmts) = do
  (result, _, _) <- checkPath annotate stmt
  case result of
    Sat   -> return $ Left ()
    Unsat -> checkPaths annotate stmts
    Undef -> error "Undef"
checkPaths _ [] = return $ Right ()

checkProgram :: (Integral n) => n -> String -> IO (Either () ())
checkProgram depth path = do
  gcl <- parseGCLfile path
  prgm <- case gcl of
    Left err -> error err
    Right prgm -> pure prgm
  let paths = listPaths $ extractPaths depth (stmt prgm)
  checkPaths (annotateForProgram prgm) paths

main :: IO ()
main = putStrLn "Hello world"
