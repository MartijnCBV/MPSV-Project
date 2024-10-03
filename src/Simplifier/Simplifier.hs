module Simplifier.Simplifier where
import Simplifier.Expr
import Simplifier.Boolean

applyLaws :: RedTypExpr -> [Law] -> RedTypExpr
applyLaws e ls = head $ applyLawsTrace e ls

applyLawsTrace :: RedTypExpr -> [Law] -> [RedTypExpr]
applyLawsTrace e ls = let e' = foldl applyLaw [e] ls
                      in  if   e == head e'
                          then e'
                          else applyLawsTrace (head e') ls ++ e'

applyLaw :: [RedTypExpr] -> Law -> [RedTypExpr]
applyLaw es l | head es == e = es
              | otherwise    = e : es
    where e = l $ head es 

laws :: [Law]
laws = blaws ++ ilaws

blaws :: [Law]
blaws = [assoc, dneg, neg, annihilate, iden, idem, compl]

ilaws :: [Law]
ilaws = []

printLawTrace :: [RedTypExpr] -> IO ()
printLawTrace es = mapM_ print $ reverse es

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

test :: IO ()
test = do
    print expr1
    printLawTrace $ applyLawsTrace (reduceTypExp expr1) laws

