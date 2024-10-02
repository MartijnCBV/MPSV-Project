module Type where

import qualified GCLParser.GCLDatatype as GDT (
  Type,
  Expr(LitI, LitB, Var, Forall, Exists, BinopExpr, Parens, ArrayElem, OpNeg, SizeOf, RepBy, Cond),
  BinOp(And, Or, Implication, Minus, Plus, Multiply, Divide, LessThan, LessThanEqual, GreaterThan, GreaterThanEqual, Equal))
import Data.Map (insert, Map, (!), empty)
import GCLParser.GCLDatatype (Program (..), VarDeclaration (VarDeclaration), Stmt (Block), Type (PType), PrimitiveType (PTInt))
import Traverse (traverseStmt)

data Op = And | Or | Implication
    | LessThan | LessThanEqual | GreaterThan | GreaterThanEqual | Equal
    | Minus | Plus | Multiply | Divide
    deriving (Eq)

instance Show Op where
  show And = "&&"
  show Or = "||"
  show Implication = "->"
  show LessThan = "<"
  show LessThanEqual = "<="
  show GreaterThan = ">"
  show GreaterThanEqual = ">="
  show Equal = "=="
  show Plus = "+"
  show Minus = "-"
  show Multiply = "*"
  show Divide = "/"

data TypedExpr
  = Var                  String GDT.Type
    | LitI               Int
    | LitB               Bool
    | Parens             TypedExpr
    | ArrayElem          TypedExpr  TypedExpr
    | OpNeg              TypedExpr
    | BinopExpr          Op         TypedExpr   TypedExpr
    | Forall             String     TypedExpr
    | Exists             String     TypedExpr
    | SizeOf             TypedExpr
    | RepBy              TypedExpr  TypedExpr   TypedExpr
    | Cond               TypedExpr  TypedExpr   TypedExpr
  deriving (Eq, Show)

convertOp :: GDT.BinOp -> Op
convertOp GDT.And              = And
convertOp GDT.Or               = Or
convertOp GDT.Implication      = Implication
convertOp GDT.Plus             = Plus
convertOp GDT.Minus            = Minus
convertOp GDT.Multiply         = Multiply
convertOp GDT.Divide           = Divide
convertOp GDT.LessThan         = LessThan
convertOp GDT.LessThanEqual    = LessThanEqual
convertOp GDT.GreaterThan      = GreaterThan
convertOp GDT.GreaterThanEqual = GreaterThanEqual
convertOp GDT.Equal            = Equal
convertOp _ = undefined

annotateWithTypes :: Map String GDT.Type -> GDT.Expr -> TypedExpr
annotateWithTypes _ (GDT.LitI val)  = LitI val
annotateWithTypes _ (GDT.LitB val)  = LitB val
annotateWithTypes varTypes (GDT.Var name)  = Var name (varTypes ! name)
annotateWithTypes varTypes (GDT.Parens op) = Parens $ annotateWithTypes varTypes op
annotateWithTypes varTypes (GDT.OpNeg op)  = OpNeg $ annotateWithTypes varTypes op
annotateWithTypes varTypes (GDT.SizeOf op) = SizeOf $ annotateWithTypes varTypes op
annotateWithTypes varTypes (GDT.Forall var expr) = Forall var (annotateWithTypes (addQuantifierVar var varTypes) expr)
annotateWithTypes varTypes (GDT.Exists var expr) = Exists var (annotateWithTypes (addQuantifierVar var varTypes) expr)
annotateWithTypes varTypes (GDT.ArrayElem array index)   = ArrayElem (annotateWithTypes varTypes array) (annotateWithTypes varTypes index)
annotateWithTypes varTypes (GDT.BinopExpr op left right) = BinopExpr (convertOp op) (annotateWithTypes varTypes left) (annotateWithTypes varTypes right)
annotateWithTypes varTypes (GDT.RepBy array index value) = RepBy (annotateWithTypes varTypes array) (annotateWithTypes varTypes index) (annotateWithTypes varTypes value)
annotateWithTypes varTypes (GDT.Cond cond left right)    = Cond (annotateWithTypes varTypes cond) (annotateWithTypes varTypes left) (annotateWithTypes varTypes right)
annotateWithTypes _ _ = undefined

-- free variables in a quantified expression (e.g. forall i :: ...) are always integers
addQuantifierVar :: String -> Map String GDT.Type -> Map String GDT.Type
addQuantifierVar name = insert name (PType PTInt)

collectVarDecls :: Stmt -> [VarDeclaration]
collectVarDecls = traverseStmt getVarDecls
  where getVarDecls (Block vardecl _) = vardecl
        getVarDecls _ = []

toMap :: [VarDeclaration] -> Map String GDT.Type
toMap = foldr addToMap empty
  where addToMap (VarDeclaration name typ) = insert name typ

programVars :: Program -> Map String GDT.Type
programVars prgm = toMap (input prgm ++ output prgm ++ collectVarDecls (stmt prgm))

annotateForProgram :: Program -> (GDT.Expr -> TypedExpr)
annotateForProgram prgm = annotateWithTypes $ programVars prgm
