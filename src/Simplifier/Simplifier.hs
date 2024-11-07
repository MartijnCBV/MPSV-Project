module Simplifier.Simplifier where
import Simplifier.Expr
import Simplifier.Boolean
import Simplifier.Theory
import Utils.Type

applyLaws :: TTExpr -> [BLaw] -> TTExpr
applyLaws e ls = head $ applyLawsTrace e ls

applyLawsTrace :: TTExpr -> [BLaw] -> [TTExpr]
applyLawsTrace e ls = let e' = foldl applyLaw [e] ls
                      in  if   e == head e'
                          then e'
                          else applyLawsTrace (head e') ls ++ e'

applyLaw :: [TTExpr] -> BLaw -> [TTExpr]
applyLaw es l | head es == e = es
              | otherwise    = e : es
  where e = l $ head es

laws :: [BLaw]
laws = applyTheoryLaws : blaws

blaws :: [BLaw]
blaws = [assocB, dnegB, negB, annihilateB, idenB, idemB, complB, morganB, quantB, compB, negCompB, elimCompB, movLCompB, movRCompB]

-- | Simplify theories
applyTheoryLaws :: BLaw
applyTheoryLaws (TTheory o e1 e2) = TTheory o (f e1) (f e2)
  where f e = foldl (\acc g -> g acc) e tlaws 
applyTheoryLaws e                 = ttApply e applyTheoryLaws

-- | Theory laws
tlaws :: [TLaw]
tlaws = [assocT, applyT, idenT, annihilateT, dnegT, negT, repByT]

printLawTrace :: [TTExpr] -> IO ()
printLawTrace es = mapM_ print $ reverse es

simplify :: TypedExpr -> TypedExpr
simplify = convertRL . flip applyLaws laws . convertLR
-- simplify e = convertRL e' `debug` ("Simplified::" ++ show e' ++ "\n")
--   where e' = applyLaws (convertLR e) laws `debug` ("Original::" ++ show e ++ "\n")

