module Tree.Wlp (getWlp, feasibleWlp, getFeasibleWlp) where

import GCLParser.GCLDatatype (Stmt (..), Expr (..), opAnd, opImplication)
import Traverse (transformExpr)

type Name = String
type Value = Expr

replace :: Name -> Value -> Expr -> Expr
replace name value = transformExpr fillVar
  where fillVar (Var n) | n == name = Just value
        fillVar _                   = Nothing

repBy :: (String -> Expr) -> String -> Expr -> Expr -> Expr
repBy f s = RepBy (f s)

opBinParens :: Expr -> (Expr -> Expr -> Expr) -> Expr -> Expr
opBinParens e1 f e2 = Parens e1 `f` Parens e2

wlpBase :: (Stmt -> Expr -> Expr) -> Stmt -> Expr -> Expr
wlpBase _ Skip                       expr = expr
wlpBase recFunc assert@(Assert _)    expr = recFunc assert expr
wlpBase recFunc assume@(Assume _)    expr = recFunc assume expr
wlpBase _ (Assign s e)               expr = replace s e expr
wlpBase recFunc (AAssign s e1 e2)    expr = flip (wlpBase recFunc) expr $ Assign s $ repBy Var s e1 e2
wlpBase recFunc (Seq s1 s2)          expr = wlpBase recFunc s1 $ wlpBase recFunc s2 expr
wlpBase _ _ _ = undefined

normalWlp :: Stmt -> Expr -> Expr
normalWlp = wlpBase wlpRec
  where wlpRec (Assert e) expr = opBinParens e opAnd expr
        wlpRec (Assume e) expr = opBinParens e opImplication expr
        wlpRec _ _ = error "unsupported"

feasibleWlp :: [Stmt] -> Expr
feasibleWlp (Skip : rest)              = feasibleWlp rest
feasibleWlp ((Assert _) : rest)        = feasibleWlp rest
feasibleWlp ((Assume e) : rest)        = opBinParens e opAnd (feasibleWlp rest)
feasibleWlp ((Assign s e) : rest)      = replace s e (feasibleWlp rest)
feasibleWlp ((AAssign s e1 e2) : rest) = feasibleWlp $ Assign s (repBy Var s e1 e2) : rest
feasibleWlp [] = LitB True
feasibleWlp _ = undefined

getWlp :: Stmt -> Expr
getWlp = flip normalWlp (LitB True)

getFeasibleWlp :: [Stmt] -> Expr
getFeasibleWlp = feasibleWlp . reverse
