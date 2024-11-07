{- | 
This module contains all laws having to do with boolean logic
-}
module Simplifier.Boolean2 where

import Simplifier.Expr2
import Data.List
import Debug.Trace

debug :: c -> String -> c
debug = flip trace

-- | Helper function for applying laws
ttApply :: TTExpr -> BLaw -> TTExpr
ttApply (TTOpExpr o es)     f = TTOpExpr o $ map f es
ttApply (TTOpNeg  e)        f = TTOpNeg    $ f e
ttApply (TTForall s e)      f = TTForall s $ f e
ttApply (TTExists s e)      f = TTExists s $ f e
ttApply (TTRepBy  e1 e2 e3) f = TTRepBy (f e1) (f e2) (f e3)
ttApply (TTCond   e1 e2 e3) f = TTCond  (f e1) (f e2) (f e3)
ttApply e                   _ = e

-- | Associativity law: (P /\ Q) /\ R == P /\ (Q /\ R), (P \/ Q) \/ R == P \/ (Q \/ R)
assocB :: BLaw
assocB (TTOpExpr o es) = TTOpExpr o $ sort $ concatMap f es
  where f :: TTExpr -> [TTExpr]
        f e@(TTOpExpr o' es') | o == o'   = map assocB es'
                              | otherwise = [assocB e]
        f e                   = [assocB e]
assocB e               = ttApply e assocB

-- | Identity law: P /\ true = P, P \/ false = P
idenB :: BLaw
idenB (TTOpExpr o es) = case filter (/= TTLit (o == TBAnd)) es of
                              []  -> TTLit (o == TBAnd)
                              [e] -> idenB e
                              es' -> TTOpExpr o $ map idenB es'
idenB e = ttApply e idenB

-- | Annihilation law: P /\ false = false, P \/ true = true
annihilateB :: BLaw
annihilateB (TTOpExpr TBAnd es) | TTLit False `elem` es = TTLit False
                                | otherwise             = TTOpExpr TBAnd $ map annihilateB es
annihilateB (TTOpExpr TBOr  es) | TTLit True  `elem` es = TTLit True
                                | otherwise             = TTOpExpr TBOr $ map annihilateB es
annihilateB e                   = ttApply e annihilateB

-- | Idempotence law: P /\ P = P, P \/ P = P
idemB :: BLaw
idemB (TTOpExpr o es) | null es'        = TTLit True
                      | length es' == 1 = head es'
                      | otherwise       = TTOpExpr o es'
  where es' = map idemB $ nub es
idemB e               = ttApply e idemB

-- | Complementation law: P /\ ~P = false, p \/ ~p = true
complB :: BLaw
complB (TTOpExpr o es) | or es''   = TTLit $ o /= TBAnd
                       | otherwise = TTOpExpr o es'
  where es'  = map complB es
        es'' = map (\e -> TTOpNeg e `elem` es') es'
complB e = ttApply e complB

-- | Double negation law: ~~P = P
dnegB :: BLaw
dnegB (TTOpNeg (TTOpNeg e)) = dnegB e
dnegB e                     = ttApply e dnegB

-- | Negation application: ~true = false, ~false = true, ~Ex P(x) = Vx ~P(x), ~Vx P(x) = Ex ~P(x)
negB :: BLaw
negB (TTOpNeg (TTLit b))      = TTLit      $ not b
negB (TTOpNeg (TTForall s e)) = TTExists s $ TTOpNeg e
negB (TTOpNeg (TTExists s e)) = TTForall s $ TTOpNeg e
negB e                        = ttApply e negB

-- | De Morgan's law: ~(P /\ Q) = ~P \/ ~Q, ~(P \/ Q) = ~P /\ ~Q
morganB :: BLaw
morganB (TTOpNeg (TTOpExpr o es)) = TTOpExpr o' es'
  where o' = case o of
              TBAnd -> TBOr
              TBOr  -> TBAnd
        es' = map TTOpNeg es
morganB e = ttApply e morganB

-- | Move quantifiers outwards
quantB :: BLaw
quantB (TTOpExpr o es) = foldr moveQuants (TTOpExpr o es'') quants
  where (quants, es') = partition isQuant es
        es'' = es' ++ map extractQuant quants
        isQuant (TTForall _ _) = True
        isQuant (TTExists _ _) = True
        isQuant _              = False
        extractQuant (TTForall _ e) = e
        extractQuant (TTExists _ e) = e
        extractQuant _              = error "should be unreachable"
        moveQuants (TTForall s _) acc = TTForall s acc
        moveQuants (TTExists s _) acc = TTExists s acc
        moveQuants _              _   = error "should be unreachable"
quantB e = ttApply e quantB

-- | Resolving comparisons on theory literals
compB :: BLaw
compB (TTheory o (TLit i1) (TLit i2)) = case o of
                                          TLessThan      -> TTLit (i1 < i2)
                                          TLessThanEqual -> TTLit (i1 <= i2)
                                          TEqual         -> TTLit (i1 == i2)
compB e                               = ttApply e compB

-- | Rotating negated comparisions
negCompB :: BLaw
negCompB (TTOpNeg (TTheory TLessThan      e1 e2)) = TTheory TLessThanEqual e2 e1
negCompB (TTOpNeg (TTheory TLessThanEqual e1 e2)) = TTheory TLessThan      e2 e1
negCompB e                                        = ttApply e negCompB

-- | eliminating <= comparisons
elimCompB :: BLaw
elimCompB (TTheory TLessThanEqual e1 e2) = TTheory TLessThan (TOpExpr TPlus [e1, TOpNeg $ TLit 1]) e2
elimCompB e                              = ttApply e elimCompB

-- | move literals to the left in comparisons
movLCompB :: BLaw
movLCompB e@(TTheory _ _ (TLit 0))            = e
movLCompB (TTheory o e1 (TLit i))             = TTheory o (TOpExpr TPlus [e1, TOpNeg $ TLit i]) $ TLit 0
movLCompB e@(TTheory o e1 (TOpExpr TPlus es)) | null nums = e
                                              | otherwise = TTheory o (TOpExpr TPlus (e1: map TOpNeg nums)) r
  where (nums, rest) = partition isLit es
        r = case rest of
              []  -> TLit 0
              [x] -> x
              xs  -> TOpExpr TPlus xs
-- multiplication/division not supported atm
movLCompB e                                 = ttApply e movLCompB

-- | move non-literals to the right
movRCompB :: BLaw
movRCompB e@(TTheory _ (TLit _) _) = e
movRCompB e@(TTheory o (TOpExpr TPlus es) e2) | null rest = e
                                              | otherwise = TTheory o n (TOpExpr TPlus (e2: map TOpNeg rest))
  where (nums, rest) = partition isLit es
        n = case nums of
              []  -> TLit 0
              [x] -> x
              xs  -> TOpExpr TPlus xs
-- multiplication/division not supported atm
movRCompB e = ttApply e movRCompB

isLit :: Theory -> Bool
isLit (TOpNeg (TLit _)) = True
isLit (TLit _)          = True
isLit _                 = False