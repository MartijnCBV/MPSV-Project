module Simplifier.Boolean where
import Simplifier.Expr
import Data.List

-- identity: 
-- x /\ True = x
iden :: Law
iden (RedAnd       es          ) | null es'        = RedLitB True
                                 | length es' == 1 = head es'
                                 | otherwise       = RedAnd es'
    where es' = map iden $ filter iden' es
          iden' :: RedTypExpr -> Bool
          iden' (RedLitB True) = False
          iden' _              = True
iden (RedBinopExpr o      e1 e2) = RedBinopExpr o (iden e1) (iden e2)
iden (RedOpNeg     e           ) = RedOpNeg     $ iden e
iden (RedArrayElem e1     e2   ) = RedArrayElem (iden e1) $ iden e2
iden (RedForall    s      e    ) = RedForall    s $ iden e
iden (RedExists    s      e    ) = RedExists    s $ iden e
iden (RedSizeOf    e           ) = RedSizeOf    $ iden e
iden (RedRepBy     e1     e2 e3) = RedRepBy     (iden e1) (iden e2) $ iden e3
iden (RedCond      e1     e2 e3) = RedCond      (iden e1) (iden e2) $ iden e3
iden e                           = e

-- annihilation: 
-- x /\ False = False
annihilate :: Law
annihilate (RedAnd       es          ) | RedLitB False `elem` es = RedLitB False
                                       | otherwise               = RedAnd $ map annihilate es
annihilate (RedBinopExpr o      e1 e2) = RedBinopExpr o (annihilate e1) (annihilate e2)
annihilate (RedOpNeg     e           ) = RedOpNeg     $ annihilate e
annihilate (RedArrayElem e1     e2   ) = RedArrayElem (annihilate e1) $ annihilate e2
annihilate (RedForall    s      e    ) = RedForall    s $ annihilate e
annihilate (RedExists    s      e    ) = RedExists    s $ annihilate e
annihilate (RedSizeOf    e           ) = RedSizeOf    $ annihilate e
annihilate (RedRepBy     e1     e2 e3) = RedRepBy     (annihilate e1) (annihilate e2) $ annihilate e3
annihilate (RedCond      e1     e2 e3) = RedCond      (annihilate e1) (annihilate e2) $ annihilate e3
annihilate e                           = e

-- idempotence:
-- x /\ x = x
idem :: Law
idem (RedAnd       es          ) | null es'        = RedLitB True
                                 | length es' == 1 = head es'
                                 | otherwise       = RedAnd es'
    where es' = map idem $ nub es
idem (RedBinopExpr o      e1 e2) = RedBinopExpr o (idem e1) $ idem e2
idem (RedOpNeg     e           ) = RedOpNeg     $ idem e
idem (RedArrayElem e1     e2   ) = RedArrayElem (idem e1) $ idem e2
idem (RedForall    s      e    ) = RedForall    s $ idem e
idem (RedExists    s      e    ) = RedExists    s $ idem e
idem (RedSizeOf    e           ) = RedSizeOf    $ idem e
idem (RedRepBy     e1     e2 e3) = RedRepBy     (idem e1) (idem e2) $ idem e3
idem (RedCond      e1     e2 e3) = RedCond      (idem e1) (idem e2) $ idem e3
idem e                           = e

-- complementation:
-- x /\ ~x = False
compl :: Law
compl (RedAnd es)                 | or es''   = RedLitB False
                                  | otherwise = RedAnd es'
    where es'  = map compl es
          es'' = map (\e -> RedOpNeg e `elem` es') es'
compl (RedBinopExpr o      e1 e2) = RedBinopExpr o (compl e1) $ compl e2
compl (RedOpNeg     e           ) = RedOpNeg     $ compl e
compl (RedArrayElem e1     e2   ) = RedArrayElem (compl e1) $ compl e2
compl (RedForall    s      e    ) = RedForall    s $ compl e
compl (RedExists    s      e    ) = RedExists    s $ compl e
compl (RedSizeOf    e           ) = RedSizeOf    $ compl e
compl (RedRepBy     e1     e2 e3) = RedRepBy     (compl e1) (compl e2) $ compl e3
compl (RedCond      e1     e2 e3) = RedCond      (compl e1) (compl e2) $ compl e3
compl e                           = e

-- double negation: 
-- ~~x = x
dneg :: Law
dneg (RedOpNeg     (RedOpNeg e)) = dneg e
dneg (RedOpNeg     e           ) = RedOpNeg     $ dneg e
dneg (RedBinopExpr o      e1 e2) = RedBinopExpr o (dneg e1) $ dneg e2
dneg (RedAnd       es          ) = RedAnd       $ map dneg es
dneg (RedArrayElem e1     e2   ) = RedArrayElem (dneg e1) $ dneg e2
dneg (RedForall    s      e    ) = RedForall    s $ dneg e
dneg (RedExists    s      e    ) = RedExists    s $ dneg e
dneg (RedSizeOf    e           ) = RedSizeOf    $ dneg e
dneg (RedRepBy     e1     e2 e3) = RedRepBy     (dneg e1) (dneg e2) $ dneg e3
dneg (RedCond      e1     e2 e3) = RedCond      (dneg e1) (dneg e2) $ dneg e3
dneg e                           = e

-- negation:
-- ~True  = False
-- ~False = True
neg :: Law
neg (RedOpNeg     (RedLitB b) ) = RedLitB      $ not b
neg (RedOpNeg     e           ) = RedOpNeg     $ neg e
neg (RedBinopExpr o      e1 e2) = RedBinopExpr o (neg e1) $ neg e2
neg (RedAnd       es          ) = RedAnd       $ map neg es
neg (RedArrayElem e1     e2   ) = RedArrayElem (neg e1) $ neg e2
neg (RedForall    s      e    ) = RedForall    s $ neg e
neg (RedExists    s      e    ) = RedExists    s $ neg e
neg (RedSizeOf    e           ) = RedSizeOf    $ neg e
neg (RedRepBy     e1     e2 e3) = RedRepBy     (neg e1) (neg e2) $ neg e3
neg (RedCond      e1     e2 e3) = RedCond      (neg e1) (neg e2) $ neg e3
neg e                           = e

-- associativity:
-- (a /\ b) /\ c = a /\ (b /\ c)
assoc :: Law
assoc (RedAnd es)             = RedAnd $ sort $ concatMap f es -- needs to be sorted for use in equality check
    where f :: RedTypExpr -> [RedTypExpr]
          f (RedAnd es') = concatMap f es'
          f e            = [assoc e]
assoc (RedArrayElem e1 e2   ) = RedArrayElem (assoc e1) $ assoc e2
assoc (RedOpNeg     e       ) = RedOpNeg     $ assoc e
assoc (RedBinopExpr o  e1 e2) = RedBinopExpr o (assoc e1) $ assoc e2
assoc (RedForall    s  e    ) = RedForall    s $ assoc e
assoc (RedExists    s  e    ) = RedExists    s $ assoc e
assoc (RedSizeOf    e       ) = RedSizeOf    $ assoc e
assoc (RedRepBy     e1 e2 e3) = RedRepBy     (assoc e1) (assoc e2) $ assoc e3
assoc (RedCond      e1 e2 e3) = RedCond      (assoc e1) (assoc e2) $ assoc e3
assoc e                       = e