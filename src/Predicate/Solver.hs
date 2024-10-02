module Predicate.Solver where

import Type
import Control.Applicative
import Control.Monad ( join )
import Data.Maybe
import qualified Data.Traversable as T
import Data.List
import GCLParser.GCLDatatype (Type(PType, AType), PrimitiveType(PTInt, PTBool))

import Z3.Monad

-- | Convert an TypedExpr to a Z3 predicate which can be evaluated
toPredicate :: TypedExpr -> Z3 AST
toPredicate expr = _toPredicate expr []

-- | Convert TypedExpr to Z3 AST, while taking into account the bound vars given in the boundArgs list
_toPredicate :: TypedExpr -> [(Symbol, AST)] ->  Z3 AST
_toPredicate (Var name varType) boundArgs = do
  symbol <- mkStringSymbol name
  found <- return (find (\(argSymbol, arg) -> argSymbol == symbol) boundArgs)
  if isNothing found
    then toVarPredicate symbol varType
    else do
         (argSymbol, arg) <- return $ fromJust found
         return arg
_toPredicate (LitI i) _ = mkInteger (toInteger i)
_toPredicate (LitB b) _ = mkBool b
_toPredicate (Parens expr) bound = _toPredicate expr bound
_toPredicate (ArrayElem arrayVar@(Var name (AType PTInt)) indexExpr@(LitI i)) bound = do
  array <- toArrayPredicate name
  index <- _toPredicate indexExpr bound
  select <- mkSelect array index
  -- Add constraint: index <= length
  assert =<< mkLt index =<< mkIntVar =<< mkStringSymbol ("#" ++ name)
  return select
_toPredicate (ArrayElem arrayVar@(Var name (AType PTInt)) indexExpr@(Var _ (PType PTInt))) bound = do
  array <- toArrayPredicate name
  index <- _toPredicate indexExpr bound
  mkSelect array index
_toPredicate (OpNeg expr) bound = do
  p <- _toPredicate expr bound
  mkNot p
_toPredicate (BinopExpr op a b) bound = toBinOpPredicate op (_toPredicate a bound) (_toPredicate b bound)
_toPredicate (Forall boundVarName expr) otherBoundVars = do
  intSort <- mkIntSort
  argSymbol <- mkStringSymbol boundVarName
  arg <- mkBound 0 intSort
  mkForall [] [argSymbol] [intSort] =<< (_toPredicate expr ((argSymbol, arg):otherBoundVars))
_toPredicate (Exists boundVarName expr) otherBoundVars = do
  intSort <- mkIntSort
  argSymbol <- mkStringSymbol boundVarName
  arg <- mkBound 0 intSort
  mkExists [] [argSymbol] [intSort] =<< (_toPredicate expr ((argSymbol, arg):otherBoundVars))
_toPredicate (SizeOf (Var name (AType PTInt))) bound = _toPredicate (Var ("#" ++ name) (PType PTInt)) bound
_toPredicate (RepBy arrayVar@(Var arrayName (AType PTInt)) indexExpr@(LitI i) newValueExpr) bound = do
  array <- toArrayPredicate arrayName
  index <- _toPredicate indexExpr bound
  -- Add constraint: index <= length
  assert =<< mkLt index =<< mkIntVar =<< mkStringSymbol ("#" ++ arrayName)
  newValue <- _toPredicate newValueExpr bound
  mkStore array index newValue
_toPredicate (RepBy arrayVar@(Var arrayName (AType PTInt)) indexExpr@(Var _ (PType PTInt)) newValueExpr) bound = do
  array <- toArrayPredicate arrayName
  index <- _toPredicate indexExpr bound
  newValue <- _toPredicate newValueExpr bound
  mkStore array index newValue
_toPredicate (Cond ifExpr thenExpr elseExpr) bound = do
  ifPred <- _toPredicate ifExpr bound
  thenPred <- _toPredicate thenExpr bound
  elsePred <- _toPredicate elseExpr bound
  mkIte ifPred thenPred elsePred
_toPredicate a b = error $ "not implemented, called with: " ++ show a ++ " " ++ show b

toVarPredicate :: Symbol -> Type -> Z3 AST
toVarPredicate symbol (PType PTInt)  = mkIntVar symbol 
toVarPredicate symbol (PType PTBool) = mkBoolVar symbol
toVarPredicate symbol (AType PTInt)  = toArrayPredicate (show symbol)

toArrayPredicate :: String -> Z3 AST
toArrayPredicate name = do
  symbol <- mkStringSymbol name
  intType  <- mkIntSort
  intArrayType <- mkArraySort intType intType
  mkConst symbol intArrayType

-- | BinOp options for toPredicate
toBinOpPredicate :: Op -> Z3 AST -> Z3 AST -> Z3 AST
toBinOpPredicate And              e1 e2 = mkWithASTList mkAnd e1 e2
toBinOpPredicate Or               e1 e2 = mkWithASTList mkOr e1 e2
toBinOpPredicate Implication      e1 e2 = mkWithASTPair mkImplies e1 e2
toBinOpPredicate LessThan         e1 e2 = mkWithASTPair mkLt e1 e2
toBinOpPredicate LessThanEqual    e1 e2 = mkWithASTPair mkLe e1 e2
toBinOpPredicate GreaterThan      e1 e2 = mkWithASTPair mkGt e1 e2
toBinOpPredicate GreaterThanEqual e1 e2 = mkWithASTPair mkGe e1 e2
toBinOpPredicate Equal            e1 e2 = mkWithASTPair mkEq e1 e2
toBinOpPredicate Minus            e1 e2 = mkWithASTList mkSub e1 e2
toBinOpPredicate Plus             e1 e2 = mkWithASTList mkAdd e1 e2
toBinOpPredicate Multiply         e1 e2 = mkWithASTList mkMul e1 e2
toBinOpPredicate Divide           e1 e2 = mkWithASTPair mkDiv e1 e2
toBinOpPredicate _                _  _  = error "not implemented"

-- | Pass 2 Z3 AST arguments as a list [AST] to func
mkWithASTList ::  ([AST] -> Z3 AST) -> Z3 AST -> Z3 AST -> Z3 AST
mkWithASTList mkOperation e1 e2 = do
  a <- e1
  b <- e2
  mkOperation [a, b]

-- | Pass 2 Z3 AST arguments as a pair (AST, AST) to func
mkWithASTPair ::  (AST -> AST -> Z3 AST) -> Z3 AST -> Z3 AST -> Z3 AST
mkWithASTPair mkOperation e1 e2 = do
  a <- e1
  b <- e2
  mkOperation a b

-- | Evaluate if expression is satisfiable and with which values
assertPredicate :: TypedExpr -> [String] -> [String] -> Z3 (Result, [Maybe Integer], [Maybe Bool])
assertPredicate expr intNames boolNames = do
  predicate <- toPredicate expr
  assert predicate
  (sat, m) <- solverCheckAndGetModel
  solverReset
  if isNothing m
    then return (sat, [], [])
    else do
      -- Unnest type: [Z3 (Maybe Integer)] -> Z3 [Maybe Integer]
      intValues <- foldr (\int ints -> do 
        i <- int
        is <- ints
        return (i:is)) (return []) (map (linkAndEvalInt m) intNames)

      -- Unnest type: [Z3 (Maybe Bool)] -> Z3 [Maybe Bool]
      boolValues <- foldr (\x xs -> do 
        y <- x
        ys <- xs
        return (y:ys)) (return []) (map (linkAndEvalBool m) boolNames)

      return (sat, intValues, boolValues)

-- | Evaluate integer based on name
linkAndEvalInt :: Maybe Model -> String -> Z3 (Maybe Integer)
linkAndEvalInt Nothing      _   = return Nothing
linkAndEvalInt (Just model) str = do
  symbol <- mkStringSymbol str
  int <- mkIntVar symbol
  evalInt model int

-- | Evaluate bool based on name
linkAndEvalBool :: Maybe Model -> String -> Z3 (Maybe Bool)
linkAndEvalBool Nothing      _   = return Nothing
linkAndEvalBool (Just model) str = do
  symbol <- mkStringSymbol str
  bool <- mkBoolVar symbol
  evalBool model bool


-- TESTING FUNCS

-- | Test func to test Forall
startTestForall :: IO (Result, [Maybe Integer], [Maybe Bool])
startTestForall = evalZ3 testForall
testForall :: Z3 (Result, [Maybe Integer], [Maybe Bool])
testForall = do
  expr <- return (BinopExpr And 
                           (BinopExpr And 
                           (BinopExpr And 
                           (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 0)) (LitI 10)) 
                           (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 1)) (LitI 7)))
                           (BinopExpr Equal (SizeOf (Var "a" (AType PTInt))) (LitI 2)))                           
                           (Forall "x" (BinopExpr LessThanEqual (LitI 7) (ArrayElem (Var "a" (AType PTInt)) (Var "x" (PType PTInt))))))
  assertPredicate expr ["#a"] []

-- | Test func to test RepBy
startTestRepBy :: IO (Result, [Maybe Integer], [Maybe Bool])
startTestRepBy = evalZ3 testRepBy
testRepBy :: Z3 (Result, [Maybe Integer], [Maybe Bool])
testRepBy = do
  expr <- return (BinopExpr And 
                  (BinopExpr And 
                    (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 0)) (LitI 0)) 
                    (BinopExpr Or 
                      (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 1)) (LitI 1)) 
                      (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 2)) (LitI 2))))
                    (BinopExpr And 
                      (BinopExpr And 
                        (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 0)) (Var "x" (PType PTInt))) 
                        (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 1)) (Var "y" (PType PTInt))))
                      (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 2)) (Var "z" (PType PTInt)))))

  assertPredicate expr ["x", "y", "z"] []

-- | Test func to test RepBy
startTestBoolVar :: IO (Result, [Maybe Integer], [Maybe Bool])
startTestBoolVar = evalZ3 testBoolVar
testBoolVar :: Z3 (Result, [Maybe Integer], [Maybe Bool])
testBoolVar = do
  expr <- return (BinopExpr And 
                  (BinopExpr And 
                    (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 0)) (LitI 0)) 
                    (BinopExpr Or 
                      (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 1)) (LitI 1)) 
                      (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 2)) (LitI 2))))
                    (BinopExpr And 
                      (BinopExpr And 
                        (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 0)) (Var "x" (PType PTInt))) 
                        (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 1)) (Var "y" (PType PTInt))))
                      (BinopExpr Equal 
                        (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 2)) (LitI 2)) 
                        (Var "z" (PType PTBool)))))

  assertPredicate expr ["x", "y"] ["z"]
