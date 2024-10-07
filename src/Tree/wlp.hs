module Tree.Wlp (getWlp, getFeasibleWlp) where

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
-- these are unnecessary
-- wlpBase _ (DrefAssign s e)           expr = repBy Dereference s expr e
-- wlpBase recFunc (IfThenElse e s1 s2) expr = opBinParens (e `opAnd` recFunc s1 expr) opOr (OpNeg e `opAnd` recFunc s2 expr)
-- wlpBase _ (While _ _)                _    = error "while not supported by wlp"
-- wlpBase _ (Block _ _)                expr = expr
-- wlpBase _ (TryCatch {})              _    = error "try catch not supported by wlp"

normalWlp :: Stmt -> Expr -> Expr
normalWlp = wlpBase wlpRec
  where wlpRec (Assert e) expr = opBinParens e opAnd expr
        wlpRec (Assume e) expr = opBinParens e opImplication expr
        wlpRec _ _ = error "unsupported"

feasibleWlp :: Stmt -> Expr -> Expr
feasibleWlp = wlpBase wlpRec
  where wlpRec (Assert _) expr = expr
        wlpRec (Assume e) expr = opBinParens e opAnd expr
        wlpRec _ _ = error "unsupported"

getWlp :: Stmt -> Expr
getWlp = flip normalWlp (LitB True)

getFeasibleWlp :: Stmt -> Expr
getFeasibleWlp = flip feasibleWlp (LitB True)
