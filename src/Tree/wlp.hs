module Tree.Wlp (getWlp, getFeasibleWlp) where

import GCLParser.GCLDatatype (Stmt (..), Expr (..), opAnd, opImplication)
import Traverse (transformExpr)
import Tree.Data

type Name = String
type Value = Expr

replace :: Name -> Value -> Expr -> Expr
replace name value = transformExpr fillVar
  where fillVar (Var n) | n == name = Just value
        fillVar _                   = Nothing

opBinParens :: Expr -> (Expr -> Expr -> Expr) -> Expr -> Expr
opBinParens e1 f e2 = Parens e1 `f` Parens e2

validWlp :: [Step] -> Expr
validWlp (Left Skip : rest)                = validWlp rest
validWlp (Left ((Assert e)) : rest)        = opBinParens e opAnd (validWlp rest)
validWlp (Left ((Assume e)) : rest)        = opBinParens e opImplication (validWlp rest)
validWlp (Left ((Assign s e)) : rest)      = replace s e (validWlp rest)
validWlp (Left ((AAssign s e1 e2)) : rest) = validWlp $ Left (Assign s (RepBy (Var s) e1 e2)) : rest
validWlp (branching@(Right _) : rest)      = validWlp $ Left (getStmt branching) : rest
validWlp [] = LitB True
validWlp _ = undefined

feasibleWlp :: [Stmt] -> Expr
feasibleWlp (Skip : rest)              = feasibleWlp rest
feasibleWlp ((Assert _) : rest)        = feasibleWlp rest
feasibleWlp ((Assume e) : rest)        = opBinParens e opAnd (feasibleWlp rest)
feasibleWlp ((Assign s e) : rest)      = replace s e (feasibleWlp rest)
feasibleWlp ((AAssign s e1 e2) : rest) = feasibleWlp $ Assign s (RepBy (Var s) e1 e2) : rest
feasibleWlp [] = LitB True
feasibleWlp _ = undefined

-- validity wlp arrives in forward (front-to-back) order
getWlp :: [Step] -> Expr
getWlp = validWlp

-- feasibility wlp arrives in reverse (back-to-front) order, so reverse it
getFeasibleWlp :: Step -> [Stmt] -> Expr
getFeasibleWlp step prefix = (feasibleWlp . reverse) (getStmt step : prefix)
