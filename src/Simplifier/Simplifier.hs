module Simplifier.Simplifier where
import Simplifier.Expr
import Simplifier.Boolean
import Simplifier.Theory
import Utils.Type

-- | Apply laws without keeping a trace
applyLaws :: TTExpr -> [BLaw] -> TTExpr
applyLaws e ls = head $ applyLawsTrace e ls

-- | Apply laws and build up a trace of the effects of each law
applyLawsTrace :: TTExpr -> [BLaw] -> [TTExpr]
applyLawsTrace e ls = let e' = foldl applyLaw [e] ls
                      in  if   e == head e'
                          then e'
                          else applyLawsTrace (head e') ls ++ e'

-- | Apply a law and add the new formula to the front of the trace
applyLaw :: [TTExpr] -> BLaw -> [TTExpr]
applyLaw es l | head es == e = es
              | otherwise    = e : es
  where e = l $ head es

-- | All implemented laws (Boolean + Theory)
laws :: [BLaw]
laws = applyTheoryLaws : blaws

-- | All implemented boolean laws
blaws :: [BLaw]
blaws = [assocB, dnegB, negB, annihilateB, idenB, idemB, complB, morganB, quantB, compB, negCompB, elimCompB, movLCompB, movRCompB, subB]

-- | Simplify theories
applyTheoryLaws :: BLaw
applyTheoryLaws (TTheory o e1 e2) = TTheory o (f e1) (f e2)
  where f e = foldl (\acc g -> g acc) e tlaws 
applyTheoryLaws e                 = ttApply e applyTheoryLaws

-- | Theory laws
tlaws :: [TLaw]
tlaws = [assocT, applyT, idenT, annihilateT, dnegT, negT, repByT]

-- | Entry point to the simplifier
simplify :: TypedExpr -> TypedExpr
simplify = convertRL . flip applyLaws laws . convertLR

