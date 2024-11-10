module Tree.Wlp where

-- import GCLParser.GCLDatatype (Stmt (..), Expr (..), opAnd, opImplication)
import Tree.Data
import Utils.Type ( TypedExpr(..), opAnd, opImplication )
import GCLParser.GCLDatatype (Type)
import Utils.Traverse (transformExpr)
import Simplifier.Simplifier (simplify)

type Name = (String, Type)
type Value = TypedExpr

replace :: Name -> Value -> TypedExpr -> TypedExpr
replace (name, _) value = transformExpr fillVar
  where fillVar (Var n _) | n == name = Just value
        fillVar _                     = Nothing

opBinParens :: TypedExpr -> (TypedExpr -> TypedExpr -> TypedExpr) -> TypedExpr -> TypedExpr
opBinParens e1 f e2 = Parens e1 `f` Parens e2

validWlp :: [Step] -> TypedExpr
validWlp (Left Skip : rest)                       = validWlp rest
validWlp (Left ((Assert e)) : rest)               = opBinParens e opAnd (validWlp rest)
validWlp (Left ((Assume e)) : rest)               = opBinParens e opImplication (validWlp rest)
validWlp (Left ((Assign s e)) : rest)             = replace s e (validWlp rest)
validWlp (Left ((AAssign n@(s, t) e1 e2)) : rest) = validWlp $ Left (Assign n (RepBy (Var s t) e1 e2)) : rest
validWlp (branching@(Right _) : rest)             = validWlp $ Left (getStmt branching) : rest
validWlp [] = LitB True

feasibleWlp :: [Action] -> TypedExpr
feasibleWlp (Skip : rest)                       = feasibleWlp rest
feasibleWlp ((Assert _) : rest)                 = feasibleWlp rest
feasibleWlp ((Assume e) : rest)                 = opBinParens e opAnd (feasibleWlp rest)
feasibleWlp ((Assign s e) : rest)               = replace s e (feasibleWlp rest)
feasibleWlp (((AAssign n@(s, t) e1 e2)) : rest) = feasibleWlp $ Assign n (RepBy (Var s t) e1 e2) : rest
feasibleWlp [] = LitB True

-- feasibility wlp arrives in reverse (back-to-front) order, so reverse it
getFeasibleWlp :: Bool -> Step -> [Action] -> TypedExpr
getFeasibleWlp False step prefix = (feasibleWlp . reverse) (getStmt step : prefix)
getFeasibleWlp True step prefix  = (simplify . feasibleWlp . reverse) (getStmt step : prefix)
