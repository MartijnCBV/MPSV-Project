{-# LANGUAGE InstanceSigs #-}
module Utils.Count where

import Utils.Traverse ( traverseExpr )
import Utils.Type (TypedExpr(..), Op (And))

newtype SemigroupInt = SemigroupInt Int

toInt :: SemigroupInt -> Int
toInt (SemigroupInt i) = i

instance Semigroup SemigroupInt where
  (<>) :: SemigroupInt -> SemigroupInt -> SemigroupInt
  (SemigroupInt i1) <> (SemigroupInt i2) = SemigroupInt $ i1 + i2

sizeOf :: TypedExpr -> Int
sizeOf = toInt . traverseExpr (SemigroupInt . isLeaf)
         where isLeaf (Var _ _) = 1
               isLeaf (LitB _)  = 1
               isLeaf (LitI _)  = 1
               isLeaf _         = 0

conjunctions :: TypedExpr -> Int
conjunctions = toInt . traverseExpr (SemigroupInt . isConjunction)
         where isConjunction (BinopExpr And _ _)  = 1
               isConjunction _ = 0
