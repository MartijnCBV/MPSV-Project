module Predicate.Solver where

import GCLParser.GCLDatatype
import Control.Applicative
import Control.Monad ( join )
import Data.Maybe
import qualified Data.Traversable as T

import Z3.Monad

-- | Convert an Expr to a Z3 predicate which can be evaluated
toPredicate :: Expr -> Z3 AST
toPredicate (Var name) = do --TODO support Var BOOL
  symbol <- mkStringSymbol name
  mkIntVar symbol
toPredicate (LitI i) = mkInteger (toInteger i)
toPredicate (LitB b) = mkBool b
toPredicate (Parens expr) = toPredicate expr
toPredicate (ArrayElem (Var name) indexExpr@(LitI _)) = do
  array <- toArrayPredicate name
  index <- toPredicate indexExpr
  mkSelect array index
toPredicate (OpNeg expr) = do
  p <- toPredicate expr
  mkNot p
toPredicate (BinopExpr op a b) = toBinOpPredicate op (toPredicate a) (toPredicate b)
toPredicate (Forall boundVarName expr) = do
  intSort <- mkIntSort
  varSymbol <- mkStringSymbol boundVarName
  arg <- mkBound 0 intSort
  mkForall [] [varSymbol] [intSort] =<< (toPredicate expr)
toPredicate (Exists boundVarName expr) = do
  intSort <- mkIntSort
  varSymbol <- mkStringSymbol boundVarName
  arg <- mkBound 0 intSort
  mkExists [] [varSymbol] [intSort] =<< (toPredicate expr)
toPredicate (SizeOf (Var name)) = do
  length <- toPredicate (Var ("#" ++ name))
  -- Forall i: i >= 0 && i < length
  -- (i is renamed to i#name to ensure uniqueness)
  lengthConstraint <- toPredicate $ Forall ("i#" ++ name) 
    (BinopExpr And (BinopExpr GreaterThanEqual (Var ("i#" ++ name)) (LitI 0)) 
    (BinopExpr LessThan (Var ("i#" ++ name)) (Var ("#" ++ name))))
  assert lengthConstraint
  return length
toPredicate (RepBy (Var arrayName) indexExpr newValueExpr) = do
  array <- toArrayPredicate arrayName
  index <- toPredicate indexExpr
  newValue <- toPredicate newValueExpr
  mkStore array index newValue
toPredicate (Cond ifExpr thenExpr elseExpr) = do
  ifPred <- toPredicate ifExpr
  thenPred <- toPredicate thenExpr
  elsePred <- toPredicate elseExpr
  mkIte ifPred thenPred elsePred
toPredicate _ = error "not implemented"

toArrayPredicate :: String -> Z3 AST
toArrayPredicate name = do
  symbol <- mkStringSymbol name
  int_type  <- mkIntSort
  int_array_type <- mkArraySort int_type int_type
  mkConst symbol int_array_type

-- | BinOp options for toPredicate
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

-- | Pass 2 Z3 AST arguments as a list [AST] to func
mkWithASTList ::  ([AST] -> Z3 AST) -> Z3 AST -> Z3 AST -> Z3 AST
mkWithASTList mkOperation e1 e2  =  do
  a <- e1
  b <- e2
  mkOperation [a, b]

-- | Pass 2 Z3 AST arguments as a pair (AST, AST) to func
mkWithASTPair ::  (AST -> AST -> Z3 AST) -> Z3 AST -> Z3 AST -> Z3 AST
mkWithASTPair mkOperation e1 e2  =  do
  a <- e1
  b <- e2
  mkOperation a b

-- | Evaluate if expression is satisfiable and with which values
assertPredicate :: Expr -> [String] -> [String] -> Z3 (Result, [Maybe Integer])
-- assertPredicate :: Expr -> [String] -> [String] -> Z3 (Result, [Maybe Integer], [Maybe Bool])
assertPredicate expr intNames _ = do
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

-- | Evaluate integer based on name
linkAndEvalInt :: Maybe Model -> String -> Z3 (Maybe Integer)
linkAndEvalInt Nothing _ = return Nothing
linkAndEvalInt (Just model) str = do
  symbol <- mkStringSymbol str
  int <- mkIntVar symbol
  evalInt model int

-- TODO: booleans!
-- | Evaluate bool based on name
-- linkAndEvalBool :: Maybe Model -> String -> Z3 (Maybe Bool)
-- linkAndEvalBool Nothing _ = return Nothing
-- linkAndEvalBool (Just model) str = do
--   symbol <- mkStringSymbol str
--   bool <- mkBoolVar symbol
--   evalBool model bool



testExprBinOp :: Expr
testExprBinOp = BinopExpr And (BinopExpr And a b) c
  where a = BinopExpr GreaterThan (Var "a") (LitI 3)
        b = BinopExpr Equal (Var "a") (ArrayElem (Var "b") (LitI 1))
        c = BinopExpr Equal (Var "c") (ArrayElem (Var "b") (LitI 1))

-- (forall i :: ((0<=i && (i< #a)) ==>  (a[i] >= a[0]))) 
testExprForall :: Expr
testExprForall = Forall "i" (BinopExpr Implication lengthCheck elementCheck)
  where lengthCheck = BinopExpr And (BinopExpr LessThanEqual (LitI 0) (Var "i")) (BinopExpr LessThanEqual (Var "i") (SizeOf (Var "a")))
        elementCheck = BinopExpr GreaterThanEqual (ArrayElem (Var "a") (Var "i")) (ArrayElem (Var "a") (LitI 0))

testPredicate :: Expr -> [String] -> [String] -> IO ()
testPredicate expr intNames boolNames = do
   r <- evalZ3 (assertPredicate expr intNames boolNames)
   print r



testDefaultPredicate :: IO ()
testDefaultPredicate = testPredicate testExprForall ["i", "a"] []


testFA :: Z3 Result 
testFA = do
  intSort <- mkIntSort
  arraySort <- mkArraySort intSort intSort
  a <- mkFreshVar "a" arraySort
  _0 <- mkInteger 0
  _1 <- mkInteger 1
  _10 <- mkInteger 10
  _7 <- mkInteger 7
  _5 <- mkInteger 50
  assert =<< mkEq _10 =<< mkSelect a _0
  assert =<< mkEq _7 =<< mkSelect a _1
  x <- mkStringSymbol "x"
  arg <- mkBound 0 intSort
  xint <- mkConst x intSort
  assert =<< mkForall [] [x] [intSort] =<< mkLe _5 =<< mkSelect a arg
  (sat, m) <- solverCheckAndGetModel
  return sat

testSFA = evalZ3 testFA