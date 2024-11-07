{- |
This module contains all laws having to do with the theory of integers
-}

module Simplifier.Theory where

import Simplifier.Expr
import Data.List

-- | Helper function for applying laws
tApply :: Theory -> TLaw -> Theory
tApply (TArrayElem e1 e2)    f = TArrayElem (f e1) (f e2)
tApply (TSizeOf    e)        f = TSizeOf   $ f e
tApply (TOpNeg     e)        f = TOpNeg    $ f e
tApply (TOpExpr    o  es)    f = TOpExpr o $ map f es
tApply (TBinopExpr o  e1 e2) f = TBinopExpr o (f e1) (f e2)
tApply (TRepBy     e1 e2 e3) f = TRepBy (f e1) (f e2) (f e3)
tApply e _ = e

-- | associativity
assocT :: TLaw
assocT (TOpExpr o es)    = TOpExpr o $ sort $ concatMap f es
  where f :: Theory -> [Theory]
        f e@(TOpExpr o' es') | o == o'   = map assocT es'
                             | otherwise = [assocT e]
        f e                  = [assocT e]
assocT e                 = tApply e assocT

-- | application
applyT :: TLaw
applyT (TOpExpr    o         es)                  = case o of
                                                      TPlus     -> result sum     es'
                                                      TMultiply -> result product es'
  where (es', nums) = partition isI $ map applyT es
        nums'       = map extractI nums
        isI (TLit _ )         = False
        isI (TOpNeg (TLit _)) = False
        isI _                 = True
        extractI (TLit i)          = i
        extractI (TOpNeg (TLit i)) = negate i
        extractI _                 = error "should be unreachable"
        result f [] = TLit $ f nums'
        result f xs = TOpExpr o (TLit (f nums') : xs)
applyT (TBinopExpr TDivide   (TLit i1) (TLit i2)) = TLit $ i1 `div` i2
applyT (TOpNeg (TLit 0))                          = TLit 0
applyT (TOpNeg (TLit i))                          = TLit (negate i)
applyT e                                          = tApply e applyT

-- | identity
idenT :: TLaw
idenT (TOpExpr o es)                   = case filter (/= TLit iden) es of
                                            []  -> TLit iden
                                            [e] -> idenT e
                                            es' -> TOpExpr o $ map idenT es'
  where iden = case o of
                  TPlus     -> 0
                  TMultiply -> 1
idenT (TBinopExpr TDivide e1 (TLit 1)) = e1
idenT e                                = tApply e idenT

-- | annihilation
annihilateT :: TLaw
annihilateT (TOpExpr TMultiply es) | TLit 0 `elem` es' = TLit 0
                                   | otherwise         = TOpExpr TMultiply es'
  where es' = map annihilateT es
annihilateT e                      = tApply e annihilateT

-- | double negation
dnegT :: TLaw
dnegT (TOpNeg (TOpNeg e)) = e
dnegT e                   = tApply e dnegT

-- | move negation inwards on plus
negT :: TLaw
negT (TOpNeg (TOpExpr TPlus es)) = TOpExpr TPlus $ map TOpNeg es
negT e                           = tApply e negT

-- | simplify replace by
repByT :: TLaw
repByT (TArrayElem (TRepBy e1 e2 e3) e4) | e4 == e2  = e3
                                         | otherwise = TArrayElem e1 e4
repByT e                                 = tApply e repByT 