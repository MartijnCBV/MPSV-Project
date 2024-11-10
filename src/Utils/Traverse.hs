module Utils.Traverse where
import Utils.Type (TypedExpr (..))

orElse :: Maybe a -> a -> a
orElse Nothing a  = a
orElse (Just a) _ = a

transformExpr :: (TypedExpr -> Maybe TypedExpr) -> TypedExpr -> TypedExpr
transformExpr change expr@(Parens e)           = orElse (change expr) (Parens (trans e))                      where trans = transformExpr change
transformExpr change expr@(ArrayElem a e)      = orElse (change expr) (ArrayElem (trans a) (trans e))         where trans = transformExpr change
transformExpr change expr@(OpNeg e)            = orElse (change expr) (OpNeg (trans e))                       where trans = transformExpr change
transformExpr change expr@(BinopExpr op e1 e2) = orElse (change expr) (BinopExpr op (trans e1) (trans e2))    where trans = transformExpr change
transformExpr change expr@(Forall n e)         = orElse (change expr) (Forall n (trans e))                    where trans = transformExpr change
transformExpr change expr@(Exists n e)         = orElse (change expr) (Exists n (trans e))                    where trans = transformExpr change
transformExpr change expr@(SizeOf a)           = orElse (change expr) (SizeOf (trans a))                      where trans = transformExpr change
transformExpr change expr@(RepBy a e1 e2)      = orElse (change expr) (RepBy (trans a) (trans e1) (trans e2)) where trans = transformExpr change
transformExpr change expr@(Cond g e1 e2)       = orElse (change expr) (Cond (trans g) (trans e1) (trans e2))  where trans = transformExpr change
transformExpr change expr                      = orElse (change expr) expr

traverseExpr :: (Semigroup m) => (TypedExpr -> m) -> TypedExpr -> m
traverseExpr get expr@(Parens e)          = get expr <> traverseExpr get e
traverseExpr get expr@(ArrayElem a e)     = get expr <> traverseExpr get a <> traverseExpr get e
traverseExpr get expr@(OpNeg e)           = get expr <> traverseExpr get e
traverseExpr get expr@(BinopExpr _ e1 e2) = get expr <> traverseExpr get e1 <> traverseExpr get e2
traverseExpr get expr@(Forall _ e)        = get expr <> traverseExpr get e
traverseExpr get expr@(Exists _ e)        = get expr <> traverseExpr get e
traverseExpr get expr@(SizeOf a)          = get expr <> traverseExpr get a
traverseExpr get expr@(RepBy a e1 e2)     = get expr <> traverseExpr get a <> traverseExpr get e1 <> traverseExpr get e2
traverseExpr get expr@(Cond g e1 e2)      = get expr <> traverseExpr get g <> traverseExpr get e1 <> traverseExpr get e2
traverseExpr get expr                     = get expr
