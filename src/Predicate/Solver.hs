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
  symbol <- mkStringSymbol name
  int_type  <- mkIntSort
  int_array_type <- mkArraySort int_type int_type
  array <- mkConst symbol int_array_type

  index <- toPredicate indexExpr
  mkSelect array index
toPredicate (OpNeg expr) = do
  p <- toPredicate expr
  mkNot p
toPredicate (BinopExpr op a b) = toBinOpPredicate op (toPredicate a) (toPredicate b)
toPredicate (Forall freshVarName expr) = do
  mkForall 

  -- | Create a forall formula.
--
-- The bound variables are de-Bruijn indices created using 'mkBound'.
--
-- Z3 applies the convention that the last element in /xs/ refers to the
-- variable with index 0, the second to last element of /xs/ refers to the
-- variable with index 1, etc.
mkForall :: Context
          -> [Pattern]  -- ^ Instantiation patterns (see 'mkPattern').
          -> [Symbol]   -- ^ Bound (quantified) variables /xs/.
          -> [Sort]     -- ^ Sorts of the bound variables.
          -> AST        -- ^ Body of the quantifier.
          -> IO AST
-- toPredicate (Exists) = mkExists 
-- toPredicate (SizeOf) = 
-- toPredicate (RepBy) = 
-- toPredicate (Cond) = 
toPredicate _ = error "not implemented"

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
testExprForall = Forall (Var "i") (BinOp Implication lengthCheck elementCheck)
  where lengthCheck = BinopExpr And (BinOp LessThanEqual 0 (Var "i")) (BinOp LessThanEqual (Var "i") (SizeOf "a"))
        elementCheck = BinopExpr GreaterThanEqual (ArrayElem (Var "a") (Var "i")) (ArrayElem (Var "a") (LitI 0))

testPredicate :: Expr -> [String] -> [String] -> IO ()
testPredicate expr intNames boolNames = do
   r <- evalZ3 (assertPredicate expr intNames boolNames)
   print r



testDefaultPredicate :: IO ()
testDefaultPredicate = testPredicate testExprForall ["i", "a"] []