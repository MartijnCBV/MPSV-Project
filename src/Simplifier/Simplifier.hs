module Simplifier.Simplifier where
import Simplifier.Expr
import Simplifier.Boolean

applyLaws :: RedTypExpr -> [Law] -> RedTypExpr
applyLaws e ls = let e' = foldl (\acc law -> law acc) e ls
                 in  if   e == e'
                     then e
                     else applyLaws e' ls

laws :: [Law]
laws = blaws ++ ilaws

blaws :: [Law]
blaws = [assoc, dneg, neg, annihilate, iden, idem, compl]

ilaws :: [Law]
ilaws = []

expr1 :: TypExpr
expr1 = Parens (BinopExpr And
        (BinopExpr Or
            (OpNeg (BinopExpr Implication (LitB True) (LitB False)))  -- not (True -> False)
            (BinopExpr Implication (OpNeg (LitB False)) (LitB True))  -- not False -> True
        )
        (BinopExpr Implication
            (OpNeg (BinopExpr Or (LitB False) (LitB True)))  -- not (False or True)
            (BinopExpr And (LitB True) (LitB True))          -- True and True
        )
    )

expr2 :: RedTypExpr
expr2 = reduceTypExp expr1


test :: IO ()
test = do
    print expr1
    print "-------------------------------------------------"
    print expr2
    print "-------------------------------------------------"
    print $ applyLaws expr2 laws

