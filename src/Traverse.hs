module Traverse where

import GCLParser.GCLDatatype

orElse :: Maybe a -> a -> a
orElse Nothing a  = a
orElse (Just a) _ = a

transformExpr :: (Expr -> Maybe Expr) -> Expr -> Expr
transformExpr change expr@(Parens e)           = orElse (change expr) (Parens (trans e))                      where trans = transformExpr change
transformExpr change expr@(ArrayElem a e)      = orElse (change expr) (ArrayElem (trans a) (trans e))         where trans = transformExpr change
transformExpr change expr@(OpNeg e)            = orElse (change expr) (OpNeg (trans e))                       where trans = transformExpr change
transformExpr change expr@(BinopExpr op e1 e2) = orElse (change expr) (BinopExpr op (trans e1) (trans e2))    where trans = transformExpr change
transformExpr change expr@(Forall n e)         = orElse (change expr) (Forall n (trans e))                    where trans = transformExpr change
transformExpr change expr@(Exists n e)         = orElse (change expr) (Exists n (trans e))                    where trans = transformExpr change
transformExpr change expr@(SizeOf a)           = orElse (change expr) (SizeOf (trans a))                      where trans = transformExpr change
transformExpr change expr@(RepBy a e1 e2)      = orElse (change expr) (RepBy (trans a) (trans e1) (trans e2)) where trans = transformExpr change
transformExpr change expr@(Cond g e1 e2)       = orElse (change expr) (Cond (trans g) (trans e1) (trans e2))  where trans = transformExpr change
transformExpr change expr@(NewStore e)         = orElse (change expr) (NewStore (trans e))                    where trans = transformExpr change
transformExpr change expr                      = orElse (change expr) expr

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

traverseStmt :: (Semigroup m) => (Stmt -> m) -> Stmt -> m
traverseStmt get stmt@(Seq stmt1 stmt2) = get stmt <> traverseStmt get stmt1 <> traverseStmt get stmt2
traverseStmt get stmt@(IfThenElse _ stmt1 stmt2) = get stmt <> traverseStmt get stmt1 <> traverseStmt get stmt2
traverseStmt get stmt@(While _ body) = get stmt <> traverseStmt get body
traverseStmt get stmt@(Block _ block) = get stmt <> traverseStmt get block
traverseStmt get stmt@(TryCatch _ try catch) = get stmt <> traverseStmt get try <> traverseStmt get catch
traverseStmt get stmt = get stmt
