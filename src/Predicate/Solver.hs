module Predicate.Solver where

import Utils.Type
import Data.Maybe
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
  let found = find (\(argSymbol, _) -> argSymbol == symbol) boundArgs
  if isNothing found
    then toVarPredicate symbol varType
    else do
         (_, arg) <- return $ fromJust found
         return arg
_toPredicate (LitI i) _ = mkInteger (toInteger i)
_toPredicate (LitB b) _ = mkBool b
_toPredicate (Parens expr) bound = _toPredicate expr bound
_toPredicate (ArrayElem arrayVar indexExpr@(Var _ (PType PTInt))) bound = do
  array <- toArrayPredicate arrayVar bound
  index <- _toPredicate indexExpr bound
  mkSelect array index
_toPredicate (ArrayElem arrayVar indexExpr) bound = do
  array <- toArrayPredicate arrayVar bound
  index <- _toPredicate indexExpr bound
  select <- mkSelect array index
  -- Add constraint: index <= length
  assert =<< mkLt index =<< mkIntVar =<< mkStringSymbol ("#" ++ getArrayName arrayVar)
  return select
_toPredicate (OpNeg expr) bound = do
  p <- _toPredicate expr bound
  mkNot p
_toPredicate (BinopExpr op a b) bound = toBinOpPredicate op (_toPredicate a bound) (_toPredicate b bound)
_toPredicate (Forall boundVarName expr) otherBoundVars = do
  intSort <- mkIntSort
  argSymbol <- mkStringSymbol boundVarName
  arg <- mkBound 0 intSort
  mkForall [] [argSymbol] [intSort] =<< _toPredicate expr ((argSymbol, arg):otherBoundVars)
_toPredicate (Exists boundVarName expr) otherBoundVars = do
  intSort <- mkIntSort
  argSymbol <- mkStringSymbol boundVarName
  arg <- mkBound 0 intSort
  mkExists [] [argSymbol] [intSort] =<< _toPredicate expr ((argSymbol, arg):otherBoundVars)
_toPredicate (SizeOf (Var name (AType PTInt))) bound = _toPredicate (Var ("#" ++ name) (PType PTInt)) bound
_toPredicate (SizeOf (RepBy array _ _)) bound = _toPredicate (SizeOf array) bound
_toPredicate (RepBy arrayVar indexExpr@(Var _ (PType PTInt)) newValueExpr) bound = do
  array <- toArrayPredicate arrayVar bound
  index <- _toPredicate indexExpr bound
  newValue <- _toPredicate newValueExpr bound
  mkStore array index newValue
_toPredicate (RepBy arrayVar indexExpr newValueExpr) bound = do
  array <- toArrayPredicate arrayVar bound
  index <- _toPredicate indexExpr bound
  -- Add constraint: index <= length
  assert =<< mkLt index =<< mkIntVar =<< mkStringSymbol ("#" ++ getArrayName arrayVar)
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
toVarPredicate symbol (AType PTInt)  = toArrayPredicate (Var (show symbol) (AType PTInt)) []
toVarPredicate _ _ = undefined

-- | Converts an array expr to a Z3 array object
toArrayPredicate :: TypedExpr ->  [(Symbol, AST)] -> Z3 AST
toArrayPredicate (Var name (AType PTInt)) _ = do
  symbol <- mkStringSymbol name
  intType  <- mkIntSort
  intArrayType <- mkArraySort intType intType
  mkConst symbol intArrayType
toArrayPredicate repby@(RepBy {}) bound = _toPredicate repby bound
toArrayPredicate expr                _     = error $ show expr ++ " is not an array"

-- | Gets the name of an array Var or the nested array Var in a RepBy
getArrayName :: TypedExpr -> String
getArrayName (Var name (AType PTInt)) = name
getArrayName (RepBy arrayVar _ _)     = getArrayName arrayVar
getArrayName expr                     = error $ show expr ++ " is not an array"

-- | BinOp options for toPredicate
toBinOpPredicate :: Op -> Z3 AST -> Z3 AST -> Z3 AST
toBinOpPredicate And              = mkWithASTList mkAnd
toBinOpPredicate Or               = mkWithASTList mkOr
toBinOpPredicate Implication      = mkWithASTPair mkImplies
toBinOpPredicate LessThan         = mkWithASTPair mkLt
toBinOpPredicate LessThanEqual    = mkWithASTPair mkLe
toBinOpPredicate GreaterThan      = mkWithASTPair mkGt
toBinOpPredicate GreaterThanEqual = mkWithASTPair mkGe
toBinOpPredicate Equal            = mkWithASTPair mkEq
toBinOpPredicate Minus            = mkWithASTList mkSub
toBinOpPredicate Plus             = mkWithASTList mkAdd
toBinOpPredicate Multiply         = mkWithASTList mkMul
toBinOpPredicate Divide           = mkWithASTPair mkDiv

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
assertPredicate :: TypedExpr -> [String] -> [String] -> [String] -> Z3 (Result, [Maybe Integer], [Maybe Bool], [Maybe String])
assertPredicate expr intNames boolNames arrayNames = do
  assert =<< toPredicate expr
  (sat, m) <- solverCheckAndGetModel
  evaluateResult sat m intNames boolNames arrayNames

evaluateResult :: Result -> Maybe Model -> [String] -> [String] -> [String] -> Z3 (Result, [Maybe Integer], [Maybe Bool], [Maybe String])
evaluateResult result Nothing _        _         _          = do
  solverReset
  return (result, [], [], [])
evaluateResult result _       []       []        []         = do
  solverReset
  return (result, [], [], [])
evaluateResult _      m1       intNames boolNames arrayNames = do
  -- If SAT, evaluate array length and add var for each index under #a
  _ <- foldr ((\x xs -> do
    y <- x
    ys <- xs
    return (y:ys)) . linkArray m1) (return []) arrayNames
  -- Solve again to evaluate array with new asserts
  (sat, m2) <- solverCheckAndGetModel

  -- Unnest type: [Z3 (Maybe Integer)] -> Z3 [Maybe Integer]
  intValues <- foldr ((\int ints -> do
    i <- int
    is <- ints
    return (i:is)) . linkAndEvalInt m2) (return []) intNames

  -- Unnest type: [Z3 (Maybe Bool)] -> Z3 [Maybe Bool]
  boolValues <- foldr ((\x xs -> do
    y <- x
    ys <- xs
    return (y:ys)) . linkAndEvalBool m2) (return []) boolNames

  -- Unnest type: [Z3 (Maybe String)] -> Z3 [Maybe String]
  arrayValues <- foldr ((\x xs -> do
    y <- x
    ys <- xs
    return (y:ys)) . customEvalArray m2) (return []) arrayNames

  solverReset
  return (sat, intValues, boolValues, arrayValues)

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

-- | Assign vars to each index of an array based on length
linkArray :: Maybe Model -> String -> Z3 ()
linkArray Nothing      _   = return ()
linkArray (Just model) name = do
  maybeLength <- evalInt model =<< mkIntVar =<< mkStringSymbol ("#" ++ name)
  let arrayLength = fromMaybe 0 maybeLength
  linkArrayIndices name [0..(arrayLength-1)]

linkArrayIndices :: String -> [Integer] -> Z3 ()
linkArrayIndices _    [] = return ()
linkArrayIndices name (i:is) = do
  linkArrayIndices name is
  let indexName = "#" ++ name ++ show i
  assert =<< toPredicate (BinopExpr Equal
                         (Var indexName (PType PTInt))
                         (ArrayElem (Var name (AType PTInt)) (LitI (fromIntegral i))))

-- | Evaluate array based on name by assigning var to each index
customEvalArray :: Maybe Model -> String -> Z3 (Maybe String)
customEvalArray Nothing      _   = return Nothing
customEvalArray (Just model) name = do
  maybeLength <- evalInt model =<< mkIntVar =<< mkStringSymbol ("#" ++ name)
  let arrayLength = fromMaybe 0 maybeLength
  values <- evalArrayIndices model name [0..(arrayLength-1)]
  return (Just $ show $ catMaybes values)

evalArrayIndices :: Model -> String -> [Integer] -> Z3 [Maybe Integer]
evalArrayIndices _     _    [] = return []
evalArrayIndices model name (i:is) = do
  rest <- evalArrayIndices model name is
  let indexName = "#" ++ name ++ show i
  value <- evalInt model =<< mkIntVar =<< mkStringSymbol indexName
  return (value:rest)


-- TESTING FUNCS

-- | Test func to test Forall
startTestForall :: IO (Result, [Maybe Integer], [Maybe Bool], [Maybe String])
startTestForall = evalZ3 testForall
testForall :: Z3 (Result, [Maybe Integer], [Maybe Bool], [Maybe String])
testForall = do
  let expr = BinopExpr And
                (BinopExpr And
                (BinopExpr And
                (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 0)) (LitI 10))
                (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 1)) (LitI 7)))
                (BinopExpr Equal (SizeOf (Var "a" (AType PTInt))) (LitI 2)))
                (Forall "x" (BinopExpr LessThanEqual (LitI 7) (ArrayElem (Var "a" (AType PTInt)) (Var "x" (PType PTInt)))))
  assertPredicate expr ["#a"] [] []

-- | Test func to test RepBy
startTestRepBy :: IO (Result, [Maybe Integer], [Maybe Bool], [Maybe String])
startTestRepBy = evalZ3 testRepBy
testRepBy :: Z3 (Result, [Maybe Integer], [Maybe Bool], [Maybe String])
testRepBy = do
  let expr = BinopExpr And
              (BinopExpr And
                (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 0)) (LitI 0))
                (BinopExpr Or
                  (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 1)) (LitI 1))
                  (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 2)) (LitI 2))))
                (BinopExpr And
                  (BinopExpr And
                    (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 0)) (Var "x" (PType PTInt)))
                    (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 1)) (Var "y" (PType PTInt))))
                  (BinopExpr Equal (ArrayElem (Var "a" (AType PTInt)) (LitI 2)) (Var "z" (PType PTInt))))

  assertPredicate expr ["x", "y", "z"] [] []

-- | Test func to test RepBy
startTestBoolVar :: IO (Result, [Maybe Integer], [Maybe Bool], [Maybe String])
startTestBoolVar = evalZ3 testBoolVar
testBoolVar :: Z3 (Result, [Maybe Integer], [Maybe Bool], [Maybe String])
testBoolVar = do
  let expr = BinopExpr And
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
                    (Var "z" (PType PTBool))))

  assertPredicate expr ["x", "y"] ["z"] ["a"]

