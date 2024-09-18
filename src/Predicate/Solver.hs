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
toPredicate (Var name) = do --TODO support Var BOOL
  symbol <- (mkStringSymbol name)
  mkIntVar symbol
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
  p <- toPredicate expr
  mkNot p
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

assertPredicate :: Expr -> [String] -> [String] -> Z3 (Result, [Maybe Integer])
-- assertPredicate :: Expr -> [String] -> [String] -> Z3 (Result, [Maybe Integer], [Maybe Bool])
assertPredicate expr intNames boolNames = do
  p <- toPredicate expr
  assert p
  (sat, m) <- solverCheckAndGetModel

  intValues <- foldr (\int ints -> do 
    i <- int
    is <- ints
    return (i:is)) (return []) (map (linkAndEvalInt m) intNames)
  -- TODO: cleaner way to get [Z3 (Maybe Integer)] -> Z3 [Maybe Integer]

  -- TODO: booleans!
  -- boolValues <- foldr (\x xs -> do 
  --   y <- x
  --   ys <- xs
  --   return (y:ys)) (return []) (map (linkAndEvalBool m) boolNames)

  return (sat, intValues)

linkAndEvalInt :: Maybe Model -> String -> Z3 (Maybe Integer)
linkAndEvalInt Nothing _ = return Nothing
linkAndEvalInt (Just model) str = do
  symbol <- mkStringSymbol str
  int <- mkIntVar symbol
  evalInt model int

-- TODO: booleans!
-- linkAndEvalBool :: Maybe Model -> String -> Z3 (Maybe Bool)
-- linkAndEvalBool Nothing _ = return Nothing
-- linkAndEvalBool (Just model) str = do
--   symbol <- mkStringSymbol str
--   bool <- mkBoolVar symbol
--   evalBool model bool



testExpr :: Expr
testExpr = BinopExpr Or a b
  where a = BinopExpr GreaterThan (Var "a") (LitI 3)
        b = OpNeg (BinopExpr Equal (Var "b") (LitI 4))

testPredicate :: Expr -> [String] -> [String] -> IO ()
testPredicate expr intNames boolNames = do
   r <- evalZ3 (assertPredicate expr intNames boolNames)
   print r

testDefaultPredicate :: IO ()
testDefaultPredicate = testPredicate testExpr ["a", "b"] []