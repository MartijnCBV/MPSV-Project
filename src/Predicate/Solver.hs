module Predicate.Solver where

import GCLParser.GCLDatatype
import Control.Applicative
import Control.Monad ( join )
import Data.Maybe
import qualified Data.Traversable as T

import Z3.Monad


--
-- A simple example to construct the formula a>b && b>0, and then
-- we will SAT-check it.
--

-- script has type Z3 (...)
script = do
  a <- mkFreshIntVar "a"
  b <- mkFreshIntVar "b"
  _0 <- mkInteger 0
  t1 <- mkGt a b
  t2 <- mkGt b _0
  f  <- mkAnd [t1,t2]

  -- a > b && b > 0 to z3 state:
  assert f
  -- SAT-check and get the model:
  (sat,Just m) <- solverCheckAndGetModel
  aVal <- evalInt m a
  bVal <- evalInt m b
  return(sat,aVal,bVal)


main :: IO ()
main = do
   r <- evalZ3 script
   putStrLn . show $ r


-------------------------------------

toPredicate :: Expr -> Z3 AST
toPredicate (Var name) = mkFreshIntVar name
toPredicate (LitI i) = mkInteger (toInteger i)
toPredicate (LitB b) = mkBool b
toPredicate (Parens expr) = toPredicate expr
toPredicate (ArrayElem (Var name) i@(LitI _)) = do
  int_  <- (mkIntSort :: Z3 Sort)
  int_array <- mkArraySort int_ int_
  a_ <- mkFreshConst name int_array
  i_ <- toPredicate i
  mkSelect a_ i_
toPredicate (OpNeg expr) = do
  pred <- toPredicate expr
  mkNot pred
toPredicate (BinopExpr op a b) = toBinOpPredicate op (toPredicate a) (toPredicate b)
-- toPredicate (Forall) = mkForall 
-- toPredicate (Exists) = mkExists 
-- toPredicate (SizeOf) = 
-- toPredicate (RepBy) = 
-- toPredicate (Cond) = 
toPredicate _ = error "not implemented"

toBinOpPredicate :: BinOp -> Z3 AST -> Z3 AST -> Z3 AST
toBinOpPredicate And              e1 e2 = mkWithASTList mkAnd e1 e2
toBinOpPredicate Or               e1 e2 = mkWithASTList mkOr e1 e2
toBinOpPredicate Implication      e1 e2 = mkWithASTPair mkImplies e1 e2
toBinOpPredicate LessThan         e1 e2 = mkWithASTPair mkLt e1 e2
toBinOpPredicate LessThanEqual    e1 e2 = mkWithASTPair mkEq e1 e2
toBinOpPredicate GreaterThan      e1 e2 = mkWithASTPair mkGt e1 e2
toBinOpPredicate GreaterThanEqual e1 e2 = mkWithASTPair mkGe e1 e2
toBinOpPredicate Equal            e1 e2 = mkWithASTPair mkEq e1 e2
toBinOpPredicate Minus            e1 e2 = mkWithASTList mkSub e1 e2
toBinOpPredicate Plus             e1 e2 = mkWithASTList mkAdd e1 e2
toBinOpPredicate Multiply         e1 e2 = mkWithASTList mkMul e1 e2
toBinOpPredicate Divide           e1 e2 = mkWithASTPair mkDiv e1 e2
-- toBinOpPredicate Alias            e1 e2 = TODO
toBinOpPredicate _ _ _ = error "not implemented"

mkWithASTList ::  ([AST] -> Z3 AST) -> Z3 AST -> Z3 AST -> Z3 AST
mkWithASTList mkOperation e1 e2  =  do
  a <- e1
  b <- e2
  mkOperation [a, b]

mkWithASTPair ::  (AST -> AST -> Z3 AST) -> Z3 AST -> Z3 AST -> Z3 AST
mkWithASTPair mkOperation e1 e2  =  do
  a <- e1
  b <- e2
  mkOperation a b


testExpr :: Expr
testExpr = BinopExpr GreaterThan (Var "a") (LitI 2)

testPredicate :: Expr -> IO ()
testPredicate expr = do
   p <- evalZ3 . assertPredicate $ expr
   print p

assertPredicate :: Expr -> Z3 Result
assertPredicate expr = do
  p <- toPredicate expr
  assert p
  (sat, m) <- solverCheckAndGetModel
  return sat

testDefaultPredicate :: IO ()
testDefaultPredicate = testPredicate testExpr