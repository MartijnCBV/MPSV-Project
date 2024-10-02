{-# LANGUAGE InstanceSigs #-}
module Simplifier.Expr where

import Debug.Trace

debug :: c -> String -> c
debug = flip trace

type Law = RedTypExpr -> RedTypExpr

data Typ = IntTyp | BoolTyp | ArrayTyp Typ
    deriving (Eq, Show, Ord)

data TypExpr
    = Var                Typ String
    | LitI               Int
    | LitB               Bool
    | Parens             TypExpr
    | ArrayElem          TypExpr    TypExpr
    | OpNeg              TypExpr
    | BinopExpr          BinOp      TypExpr TypExpr
    | Forall             String     TypExpr
    | Exists             String     TypExpr
    | SizeOf             TypExpr
    | RepBy              TypExpr    TypExpr TypExpr
    | Cond               TypExpr    TypExpr TypExpr
    deriving (Eq, Show)

data BinOp = And | Or | Implication
    | LessThan | LessThanEqual | GreaterThan | GreaterThanEqual | Equal
    | Minus | Plus | Multiply | Divide
    deriving (Eq, Show)

data RedTypExpr
    = RedVar                Typ String
    | RedLitI               Int
    | RedLitB               Bool
    | RedArrayElem          RedTypExpr  RedTypExpr
    | RedOpNeg              RedTypExpr
    | RedBinopExpr          RedBinOp    RedTypExpr  RedTypExpr
    | RedAnd                [RedTypExpr]
    | RedForall             String      RedTypExpr
    | RedExists             String      RedTypExpr
    | RedSizeOf             RedTypExpr
    | RedRepBy              RedTypExpr  RedTypExpr  RedTypExpr
    | RedCond               RedTypExpr  RedTypExpr  RedTypExpr
    deriving (Eq, Ord)

instance Show RedTypExpr where
    show :: RedTypExpr -> String
    show (RedVar       _  s        ) = s
    show (RedLitI      i           ) = show i
    show (RedLitB      b           ) = if b then "T" else "F"
    show (RedArrayElem e1 e2       ) = show e1 ++ '[' : show e2 ++ "]"
    show (RedOpNeg     (RedOpNeg e)) = '~' : show (RedOpNeg e )
    show (RedOpNeg     (RedLitB  b)) = '~' : show (RedLitB  b )
    show (RedOpNeg     (RedAnd  es)) = '~' : show (RedAnd   es)
    show (RedOpNeg     e           ) = "~(" ++ show e ++ ")"
    show (RedBinopExpr o  e1 e2    ) = '(' : show e1 ++ ' ' : show o ++ ' ' : show e2 ++ ")"
    show (RedAnd       es          ) = "/\\ " ++ show es
    show (RedForall    s  e        ) = "\\-/ " ++ show s ++ '(' : show e ++ ")"
    show (RedExists    s  e        ) = "E " ++ show s ++ '(' : show e ++ ")"
    show (RedSizeOf    e           ) = "#(" ++ show e ++ ")"
    show _                           = "undefined"

data RedBinOp 
    = RedLessThan | RedEqual
    | RedMinus | RedPlus | RedMultiply | RedDivide
    deriving (Eq, Ord)

instance Show RedBinOp where
    show :: RedBinOp -> String
    show RedLessThan = "<"
    show RedEqual    = "="
    show RedMinus    = "-"
    show RedPlus     = "+"
    show RedMultiply = "*"
    show RedDivide   = "/"

reduceTypExp :: TypExpr -> RedTypExpr
reduceTypExp (Var       t  s    ) = RedVar          t                 s
reduceTypExp (LitI      i       ) = RedLitI         i
reduceTypExp (LitB      b       ) = RedLitB         b
reduceTypExp (Parens    e       ) = reduceTypExp e
reduceTypExp (ArrayElem e1 e2   ) = RedArrayElem    (reduceTypExp e1) $ reduceTypExp e2
reduceTypExp (OpNeg     e       ) = RedOpNeg        $ reduceTypExp e
reduceTypExp (BinopExpr o  e1 e2) = reduceBinOpExpr o                 (reduceTypExp e1) $ reduceTypExp e2
reduceTypExp (Forall    s  e    ) = RedForall       s                 $ reduceTypExp e
reduceTypExp (Exists    s  e    ) = RedExists       s                 $ reduceTypExp e
reduceTypExp (SizeOf    e       ) = RedSizeOf       $ reduceTypExp e
reduceTypExp (RepBy     e1 e2 e3) = RedRepBy        (reduceTypExp e1) (reduceTypExp e2) $ reduceTypExp e3
reduceTypExp (Cond      e1 e2 e3) = RedCond         (reduceTypExp e1) (reduceTypExp e2) $ reduceTypExp e3

reduceBinOpExpr :: BinOp -> RedTypExpr -> RedTypExpr -> RedTypExpr
reduceBinOpExpr And              e1 e2 = RedAnd          [e1, e2]
reduceBinOpExpr Or               e1 e2 = RedOpNeg        $ RedAnd [RedOpNeg e1, RedOpNeg e2]
reduceBinOpExpr Implication      e1 e2 = reduceBinOpExpr Or          (RedOpNeg e1)                         e2
reduceBinOpExpr LessThan         e1 e2 = RedBinopExpr    RedLessThan e1                                    e2
reduceBinOpExpr LessThanEqual    e1 e2 = reduceBinOpExpr Or          (RedBinopExpr RedLessThan e1 e2)      $ RedBinopExpr RedEqual e1 e2
reduceBinOpExpr GreaterThan      e1 e2 = RedOpNeg        $ reduceBinOpExpr LessThanEqual e1 e2
reduceBinOpExpr GreaterThanEqual e1 e2 = reduceBinOpExpr Or          (reduceBinOpExpr GreaterThan e1 e2)   $ RedBinopExpr RedEqual e1 e2
reduceBinOpExpr Equal            e1 e2 = RedBinopExpr    RedEqual    e1                                    e2
reduceBinOpExpr Minus            e1 e2 = RedBinopExpr    RedMinus    e1                                    e2
reduceBinOpExpr Plus             e1 e2 = RedBinopExpr    RedPlus     e1                                    e2
reduceBinOpExpr Multiply         e1 e2 = RedBinopExpr    RedMultiply e1                                    e2
reduceBinOpExpr Divide           e1 e2 = RedBinopExpr    RedDivide   e1                                    e2

expandRedTypExp :: RedTypExpr -> TypExpr
expandRedTypExp (RedVar       t  s    ) = Var       t                    s
expandRedTypExp (RedLitI      i       ) = LitI      i
expandRedTypExp (RedLitB      b       ) = LitB      b
expandRedTypExp (RedArrayElem e1 e2   ) = ArrayElem (expandRedTypExp e1) $ expandRedTypExp e2
expandRedTypExp (RedOpNeg     e       ) = OpNeg     $ expandRedTypExp e
expandRedTypExp (RedBinopExpr o  e1 e2) = BinopExpr (expandRedBinOp o)   (expandRedTypExp e1) $ expandRedTypExp e2
expandRedTypExp (RedAnd       (e:es)  ) = foldr (\i acc -> BinopExpr And acc $ expandRedTypExp i) (expandRedTypExp e) es
expandRedTypExp (RedAnd       []      ) = error "can not have empty and expression"
expandRedTypExp (RedForall    s  e    ) = Forall    s                    $ expandRedTypExp e
expandRedTypExp (RedExists    s  e    ) = Exists    s                    $ expandRedTypExp e
expandRedTypExp (RedSizeOf    e       ) = SizeOf    $ expandRedTypExp e
expandRedTypExp (RedRepBy     e1 e2 e3) = RepBy     (expandRedTypExp e1) (expandRedTypExp e2) $ expandRedTypExp e3
expandRedTypExp (RedCond      e1 e2 e3) = Cond      (expandRedTypExp e1) (expandRedTypExp e2) $ expandRedTypExp e3

expandRedBinOp :: RedBinOp -> BinOp
expandRedBinOp RedLessThan = LessThan
expandRedBinOp RedEqual    = Equal
expandRedBinOp RedMinus    = Minus
expandRedBinOp RedPlus     = Plus
expandRedBinOp RedMultiply = Multiply
expandRedBinOp RedDivide   = Divide