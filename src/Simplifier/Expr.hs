{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Simplifier.Expr where


type Law   = RedTypExpr -> RedTypExpr
type Merge = RedTypExpr -> RedTypExpr -> RedTypExpr


class Convertable a b where
    convert :: a -> b


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
    deriving (Eq)


data BinOp = And | Or | Implication
    | LessThan | LessThanEqual | GreaterThan | GreaterThanEqual | Equal
    | Minus | Plus | Multiply | Divide
    deriving (Eq)


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


data RedBinOp
    = RedLessThan | RedEqual
    | RedMinus | RedPlus | RedMultiply | RedDivide
    deriving (Eq, Ord)


instance Show TypExpr where
    show :: TypExpr -> String
    show (Var       _  s        ) = s
    show (LitI      i           ) = show i
    show (LitB      b           ) = if b then "T" else "F"
    show (Parens    e           ) = '(' : show e ++ ")"
    show (ArrayElem e1 e2       ) = show e1 ++ '[' : show e2 ++ "]"
    show (OpNeg     e           ) = "~" ++ show e
    show (BinopExpr o  e1 e2    ) = '(' : show e1 ++ ' ' : show o ++ ' ' : show e2 ++ ")"
    show (Forall    s  e        ) = "\\-/ " ++ show s ++ '(' : show e ++ ")"
    show (Exists    s  e        ) = "E " ++ show s ++ '(' : show e ++ ")"
    show (SizeOf    e           ) = "#(" ++ show e ++ ")"
    show _                           = "undefined"


instance Show BinOp where
    show :: BinOp -> String
    show And              = "/\\"
    show Or               = "\\/"
    show Implication      = "=>"
    show LessThan         = "<"
    show LessThanEqual    = "<="
    show GreaterThan      = ">"
    show GreaterThanEqual = ">="
    show Equal            = "="
    show Minus            = "-"
    show Plus             = "+"
    show Multiply         = "*"
    show Divide           = "/"


instance Show RedTypExpr where
    show :: RedTypExpr -> String
    show (RedVar       _  s        ) = s
    show (RedLitI      i           ) = show i
    show (RedLitB      b           ) = if b then "T" else "F"
    show (RedArrayElem e1 e2       ) = show e1 ++ '[' : show e2 ++ "]"
    show (RedOpNeg     e           ) = "~" ++ show e
    show (RedBinopExpr o  e1 e2    ) = '(' : show e1 ++ ' ' : show o ++ ' ' : show e2 ++ ")"
    show (RedAnd       es          ) = "/\\ " ++ show es
    show (RedForall    s  e        ) = "\\-/ " ++ show s ++ '(' : show e ++ ")"
    show (RedExists    s  e        ) = "E " ++ show s ++ '(' : show e ++ ")"
    show (RedSizeOf    e           ) = "#(" ++ show e ++ ")"
    show _                           = "undefined"


instance Show RedBinOp where
    show :: RedBinOp -> String
    show RedLessThan = "<"
    show RedEqual    = "="
    show RedMinus    = "-"
    show RedPlus     = "+"
    show RedMultiply = "*"
    show RedDivide   = "/"


instance Convertable TypExpr RedTypExpr where
    convert :: TypExpr -> RedTypExpr
    convert (Var       t  s    ) = RedVar          t                 s
    convert (LitI      i       ) = RedLitI         i
    convert (LitB      b       ) = RedLitB         b
    convert (Parens    e       ) = convert e
    convert (ArrayElem e1 e2   ) = RedArrayElem    (convert e1) $ convert e2
    convert (OpNeg     e       ) = RedOpNeg        $ convert e
    convert (BinopExpr o  e1 e2) = (convert o :: Merge) (convert e1) (convert e2)
    convert (Forall    s  e    ) = RedForall       s                 $ convert e
    convert (Exists    s  e    ) = RedExists       s                 $ convert e
    convert (SizeOf    e       ) = RedSizeOf       $ convert e
    convert (RepBy     e1 e2 e3) = RedRepBy        (convert e1) (convert e2) $ convert e3
    convert (Cond      e1 e2 e3) = RedCond         (convert e1) (convert e2) $ convert e3


instance Convertable BinOp Merge where
    convert :: BinOp -> Merge
    convert And              = \e1 e2 -> RedAnd [e1, e2]
    convert Or               = \e1 e2 -> RedOpNeg $ RedAnd [RedOpNeg e1, RedOpNeg e2]
    convert Implication      = (convert Or :: Merge) . RedOpNeg
    convert LessThan         = RedBinopExpr RedLessThan
    convert LessThanEqual    = \e1 e2 -> (convert Or :: Merge) (RedBinopExpr RedLessThan e1 e2) $ RedBinopExpr RedEqual e1 e2
    convert GreaterThan      = \e1 e2 -> RedOpNeg $ (convert LessThanEqual :: Merge) e1 e2
    convert GreaterThanEqual = \e1 e2 -> (convert Or :: Merge) (convert GreaterThan e1 e2) $ RedBinopExpr RedEqual e1 e2
    convert Equal            = RedBinopExpr RedEqual
    convert Minus            = RedBinopExpr RedMinus
    convert Plus             = RedBinopExpr RedPlus
    convert Multiply         = RedBinopExpr RedMultiply
    convert Divide           = RedBinopExpr RedDivide

instance Convertable RedTypExpr TypExpr where
    convert :: RedTypExpr -> TypExpr
    convert (RedVar       t  s    ) = Var       t                    s
    convert (RedLitI      i       ) = LitI      i
    convert (RedLitB      b       ) = LitB      b
    convert (RedArrayElem e1 e2   ) = ArrayElem (convert e1) $ convert e2
    convert (RedOpNeg     e       ) = OpNeg     $ convert e
    convert (RedBinopExpr o  e1 e2) = BinopExpr (convert o)   (convert e1) $ convert e2
    convert (RedAnd       (e:es)  ) = foldr (\i acc -> BinopExpr And acc $ convert i) (convert e) es
    convert (RedAnd       []      ) = error "can not have empty and expression"
    convert (RedForall    s  e    ) = Forall    s                    $ convert e
    convert (RedExists    s  e    ) = Exists    s                    $ convert e
    convert (RedSizeOf    e       ) = SizeOf    $ convert e
    convert (RedRepBy     e1 e2 e3) = RepBy     (convert e1) (convert e2) $ convert e3
    convert (RedCond      e1 e2 e3) = Cond      (convert e1) (convert e2) $ convert e3


instance Convertable RedBinOp BinOp where
    convert :: RedBinOp -> BinOp
    convert RedLessThan = LessThan
    convert RedEqual    = Equal
    convert RedMinus    = Minus
    convert RedPlus     = Plus
    convert RedMultiply = Multiply
    convert RedDivide   = Divide