import GCLParser.GCLDatatype (Stmt (..), Expr (..), opAnd, opImplication, opOr)

repBy :: (String -> Expr) -> String -> Expr -> Expr -> Expr
repBy f s = RepBy (f s)

opBinParens :: Expr -> (Expr -> Expr -> Expr) -> Expr -> Expr
opBinParens e1 f e2 = Parens e1 `f` Parens e2

wlp :: Stmt -> Expr -> Expr
wlp Skip                 expr = expr
wlp (Assert e)           expr = opBinParens e opAnd expr
wlp (Assume e)           expr = opBinParens e opImplication expr
wlp (Assign s e)         expr = repBy Var s expr e
wlp (AAssign s e1 e2)    expr = flip wlp expr $ Assign s $ repBy Var s e1 e2
wlp (DrefAssign s e)     expr = repBy Dereference s expr e
wlp (Seq s1 s2)          expr = wlp s1 $ wlp s2 expr
wlp (IfThenElse e s1 s2) expr = opBinParens (e `opAnd` wlp s1 expr) opOr (OpNeg e `opAnd` wlp s2 expr)
wlp (While e s)          expr = unrolWhile unrolWhileK (While e s) expr
wlp (Block vs s)         expr = expr
wlp (TryCatch s s1 s2)   expr = wlp s1 expr

unrolWhileK :: Int
unrolWhileK = 100

unrolWhile :: Int -> Stmt -> Expr -> Expr
unrolWhile i (While e s) expr | i == 0 = OpNeg e `opImplication` expr
                              | i > 0  = opBinParens (e `opAnd` wlp s (unrolWhile (i - 1) (While e s) expr)) opOr (OpNeg e `opAnd` expr)
                              | otherwise = error "bad call to unrollWhile"
unrolWhile _ _ _              = error "bad call to unroleWhile"