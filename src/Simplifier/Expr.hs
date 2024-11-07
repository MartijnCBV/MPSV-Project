{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{- |
This module contains all types that have to do with the simplifier
-}
module Simplifier.Expr where

import GCLParser.GCLDatatype (Type)
import Utils.Type ( TypedExpr(..), Op(..) )

-- | A blaw is a transformation function on an expression
type BLaw = TTExpr -> TTExpr

-- | A tlaw is a transormation function on an theory expression
type TLaw = Theory -> Theory

-- | The convertable class represents two types that can be converted into each other
class Convertable a b where
    -- | Convert the left type to the right type
    convertLR :: a -> b
    -- | Convert the right type to the left type
    convertRL :: b -> a


-- | Typed expression with support for theory
data TTExpr
  = TTVar                String  Type
  | TTLit                Bool
  | TTOpNeg              TTExpr
  | TTOpExpr             TBOp   [TTExpr]
  | TTForall             String  TTExpr
  | TTExists             String  TTExpr
  | TTCond               TTExpr  TTExpr   TTExpr
  | TTheory              TCOp    Theory   Theory
  deriving (Eq, Ord)

-- | Theory represents the array and integer theories
data Theory
  = TVar               String  Type
  | TLit               Int
  | TArrayElem         Theory  Theory
  | TSizeOf            Theory
  | TOpNeg             Theory
  | TOpExpr            TOp    [Theory]
  | TBinopExpr         TBinOp  Theory   Theory
  | TRepBy             Theory  Theory   Theory
  deriving (Eq, Ord)

-- | Boolean operators
data TBOp
  = TBAnd
  | TBOr
  deriving (Eq, Ord)

-- | Comparison operators
data TCOp
  = TLessThan
  | TLessThanEqual
  | TEqual
  deriving (Eq, Ord)

-- | Theory operators that support associativity
data TOp
  = TPlus
  | TMultiply
  deriving (Eq, Ord)

-- | Theory operators that do not support associativity
data TBinOp
  = TDivide
  deriving (Eq, Ord)

instance Show TTExpr where
  show :: TTExpr -> String
  show (TTVar    s  _)     = s
  show (TTLit    b)       = show b
  show (TTOpNeg  e)       = '~' : show e
  show (TTOpExpr o  es)    = show o ++ show es
  show (TTForall s  e)     = concat ["\\-/ ", show s, "(", show e, ")"]
  show (TTExists s  e)     = concat ["E ", show s, "(", show e, ")"]
  show (TTCond   e1 e2 e3) = concat [show e1, "->", show e2, "|", show e3]
  show (TTheory  o  e1 e2) = concat ["(", show e1, show o, show e2, ")"]

instance Show Theory where
  show :: Theory -> String
  show (TVar       s  _)     = s
  show (TLit       i)        = show i
  show (TArrayElem e1 e2)    = concat [show e1, "[", show e2, "]"]
  show (TSizeOf    e)        = concat ["#(", show e, ")"]
  show (TOpNeg     e)        = '-' : show e
  show (TOpExpr    o  es)    = show o ++ show es
  show (TBinopExpr o  e1 e2) = concat ["(", show e1, show o, show e2, ")"]
  show (TRepBy     e1 e2 e3) = concat [show e1, "(", show e2, " repby ", show e3, ")"]

instance Show TBOp where
  show :: TBOp -> String
  show TBAnd = "/\\"
  show TBOr  = "\\/"

instance Show TCOp where
  show :: TCOp -> String
  show TLessThan      = "<"
  show TLessThanEqual = "<="
  show TEqual         = "="

instance Show TOp where
  show :: TOp -> String
  show TPlus     = "+"
  show TMultiply = "*"

instance Show TBinOp where
  show :: TBinOp -> String
  show TDivide = "/"

instance Convertable TypedExpr TTExpr where
  convertLR :: TypedExpr -> TTExpr
  convertLR (Var       s  t)     = TTVar s t
  convertLR (LitI      _)        = error "integers are not supported in boolean top level formulas"
  convertLR (LitB      b)        = TTLit b
  convertLR (Parens    e)        = convertLR e
  convertLR (ArrayElem _  _)     = error "array elements are not supported in boolean top level formulas"
  convertLR (OpNeg     e)        = TTOpNeg $ convertLR e
  convertLR (BinopExpr o  e1 e2) = case o of
                                    And              -> TTOpExpr TBAnd          [convertLR e1, convertLR e2]
                                    Or               -> TTOpExpr TBOr           [convertLR e1, convertLR e2]
                                    Implication      -> TTOpExpr TBOr           [TTOpNeg $ convertLR e1, convertLR e2]
                                    LessThan         -> TTheory  TLessThan      (cTheoryLR e1) (cTheoryLR e2)
                                    LessThanEqual    -> TTheory  TLessThanEqual (cTheoryLR e1) (cTheoryLR e2)
                                    GreaterThan      -> TTheory  TLessThanEqual (cTheoryLR e2) (cTheoryLR e1)
                                    GreaterThanEqual -> TTheory  TLessThan      (cTheoryLR e2) (cTheoryLR e1)
                                    Equal            -> TTheory  TEqual         (cTheoryLR e1) (cTheoryLR e2)
                                    _                -> error "operator is not supported in boolean top level formulas"
  convertLR (Forall    s  e)     = TTForall s $ convertLR e
  convertLR (Exists    s  e)     = TTExists s $ convertLR e
  convertLR (SizeOf    _)        = error "size of operations are not supported in boolean top level formulas"
  convertLR (RepBy     {})       = error "repby is not supported in boolean top level formulas"
  convertLR (Cond      e1 e2 e3) = TTCond  (convertLR e1) (convertLR e2) (convertLR e3)

  convertRL :: TTExpr -> TypedExpr
  convertRL (TTVar    s e)      = Var s e
  convertRL (TTLit    b)        = LitB b
  convertRL (TTOpNeg  e)        = OpNeg $ convertRL e
  convertRL (TTOpExpr _ [])     = error "can not have empty associative operator expression"
  convertRL (TTOpExpr o (e:es)) = let o' = case o of TBAnd -> And; TBOr -> Or
                                  in foldr (\i acc -> BinopExpr o' acc $ convertRL i) (convertRL e) es
  convertRL (TTForall s e)      = Forall s $ convertRL e
  convertRL (TTExists s e)      = Exists s $ convertRL e
  convertRL (TTCond   e1 e2 e3) = Cond  (convertRL e1) (convertRL e2) (convertRL e3)
  convertRL (TTheory  o  e1 e2) = let o' = case o of TLessThan -> LessThan; TLessThanEqual -> LessThanEqual; TEqual -> Equal
                                  in BinopExpr o' (cTheoryRL e1) (cTheoryRL e2)

-- | Helper function for 'convertLR :: TypedExpr -> TTExpr'
cTheoryLR :: TypedExpr -> Theory
cTheoryLR (Var         s  t)     = TVar s t
cTheoryLR (LitI        i)        = TLit i
cTheoryLR (LitB        _)        = error "booleans are not supported in theory"
cTheoryLR (Parens      e)        = cTheoryLR e
cTheoryLR (ArrayElem   e1 e2)    = TArrayElem (cTheoryLR e1) (cTheoryLR e2)
cTheoryLR (OpNeg       _)        = error "negations are not supported in theory"
cTheoryLR (BinopExpr   o  e1 e2) = case o of
                                    Plus             -> TOpExpr    TPlus     [cTheoryLR e1, cTheoryLR e2]
                                    Minus            -> TOpExpr    TPlus     [cTheoryLR e1, TOpNeg $ cTheoryLR e2]
                                    Multiply         -> TOpExpr    TMultiply [cTheoryLR e1, cTheoryLR e2]
                                    Divide           -> TBinopExpr TDivide   (cTheoryLR e1) (cTheoryLR e2)
                                    _                -> error "operator is not supported in theory"
cTheoryLR (Forall      _  _)     = error "forall is not supported in theory"
cTheoryLR (Exists      _  _)     = error "exists is not supported in theory"
cTheoryLR (SizeOf      e)        = TSizeOf $ cTheoryLR e
cTheoryLR (RepBy       e1 e2 e3) = TRepBy (cTheoryLR e1) (cTheoryLR e2) (cTheoryLR e3)
cTheoryLR (Cond        {})       = error "conditional is not supported in theory"

-- | Helper function for 'convertLR :: TTExpr -> TypedExpr'
cTheoryRL :: Theory -> TypedExpr
cTheoryRL (TVar         s  t)     = Var s t
cTheoryRL (TLit         i)        = LitI i
cTheoryRL (TArrayElem   e1 e2)    = ArrayElem (cTheoryRL e1) (cTheoryRL e2)
cTheoryRL (TSizeOf      e1)       = SizeOf $ cTheoryRL e1
cTheoryRL (TOpNeg       e1)       = BinopExpr Minus (LitI 0) (cTheoryRL e1)
cTheoryRL (TOpExpr      _ [])     = error "can not have empty associative operator expression"
cTheoryRL (TOpExpr      o (e:es)) = let o' = case o of TPlus -> Plus; TMultiply -> Multiply
                                    in foldr (\i acc -> BinopExpr o' acc $ cTheoryRL i) (cTheoryRL e) es
cTheoryRL (TBinopExpr   _  e1 e2) = BinopExpr Divide (cTheoryRL e1) (cTheoryRL e2)
cTheoryRL (TRepBy       e1 e2 e3) = RepBy (cTheoryRL e1) (cTheoryRL e2) (cTheoryRL e3)
