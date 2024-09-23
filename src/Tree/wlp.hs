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
wlp (While e s)          expr = error "while not supported by wlp"
wlp (Block vs s)         expr = expr
wlp (TryCatch s s1 s2)   expr = error "try catch not supported by wlp"