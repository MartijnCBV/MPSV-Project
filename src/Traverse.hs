module Traverse where

traverseExpr :: (Semigroup m) => (Expr -> m) -> Expr -> m
traverseExpr get expr@(Parens e)          = get expr <> traverseExpr get e
traverseExpr get expr@(ArrayElem a e)     = get expr <> traverseExpr get a <> traverseExpr get e
traverseExpr get expr@(OpNeg e)           = get expr <> traverseExpr get e
traverseExpr get expr@(BinopExpr _ e1 e2) = get expr <> traverseExpr get e1 <> traverseExpr get e2
traverseExpr get expr@(Forall _ e)        = get expr <> traverseExpr get e
traverseExpr get expr@(Exists _ e)        = get expr <> traverseExpr get e
traverseExpr get expr@(SizeOf a)          = get expr <> traverseExpr get a
traverseExpr get expr@(RepBy a e1 e2)     = get expr <> traverseExpr get a <> traverseExpr get e1 <> traverseExpr get e2
traverseExpr get expr@(Cond g e1 e2)      = get expr <> traverseExpr get g <> traverseExpr get e1 <> traverseExpr get e2
traverseExpr get expr@(NewStore e)        = get expr <> traverseExpr get e
traverseExpr get expr                     = get expr
