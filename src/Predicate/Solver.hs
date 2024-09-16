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
toPredicate (BinopExpr op a b) = toBinOpPredicate op a b
-- toPredicate (Forall) = mkForall 
-- toPredicate (Exists) = mkExists 
-- toPredicate (SizeOf) = 
-- toPredicate (RepBy) = 
-- toPredicate (Cond) = 
toPredicate _ = error "not implemented"

toBinOpPredicate :: BinOp -> Expr -> Expr -> Z3 AST
toBinOpPredicate _ _ _ = error "not implemented"

testPredicate :: Expr -> IO ()
testPredicate expr = do
   pred <- evalZ3 (toPredicate expr)
   putStrLn . show $ pred