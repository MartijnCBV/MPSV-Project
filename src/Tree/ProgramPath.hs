{-# LANGUAGE InstanceSigs #-}
module Tree.ProgramPath where

import GCLParser.GCLDatatype
import GCLParser.Parser ( parseGCLfile )

data UniBinTree u b = Leaf
  | Uni u (UniBinTree u b)
  | Bin b (UniBinTree u b) (UniBinTree u b)

type ControlPath = UniBinTree Stmt Expr

instance (Show u, Show b) => Show (UniBinTree u b) where
  show :: UniBinTree u b -> String
  show = printTree 0

instance (Eq u, Eq b) => Eq (UniBinTree u b) where
  (==) :: (Eq u, Eq b) => UniBinTree u b -> UniBinTree u b -> Bool
  Leaf             == Leaf             = True
  (Uni val1 rest1) == (Uni val2 rest2) = val1 == val2 && rest1 == rest2
  (Bin val1 l1 r1) == (Bin val2 l2 r2) = val1 == val2 && l1 == l2 && r1 == r2
  _                == _                = False

printTree :: (Show u, Show b) => Int -> UniBinTree u b -> String
printTree n Leaf               = replicate (n * 2) ' ' ++ "Leaf\n"
printTree n (Uni u next)       = replicate (n * 2) ' ' ++ show u ++ "\n" ++ printTree n next
printTree n (Bin b left right) = replicate (n * 2) ' ' ++ show b ++ "\n" ++ indent ++ "< LEFT >\n" ++ printTree (n + 1) left ++ indent ++ "< RIGHT >\n" ++ printTree (n + 1) right
  where indent = replicate ((n + 1) * 2) ' '

(+:) :: Stmt -> Stmt -> Stmt
(Seq lstmt1 lstmt2) +: rstmt =
  Seq lstmt1 (lstmt2 +: rstmt)
lstmt +: rstmt         = Seq lstmt rstmt

controlLeaf :: Stmt -> ControlPath
controlLeaf stmt = Uni stmt Leaf

extractPaths :: Int -> Stmt -> ControlPath
extractPaths n stmt = extractPaths' n ([] $+> stmt)

($+>) :: a -> b -> (b, a)
a $+> b = (b, a)
infixr 0 $+>

extractPaths' :: Int -> (Stmt, [Stmt]) -> ControlPath
extractPaths' 0 _                            = Leaf
extractPaths' _ (stmt@Skip, handles)         = controlLeaf stmt
extractPaths' _ (stmt@(Assert {}), handles)  = controlLeaf stmt
extractPaths' _ (stmt@(Assume {}), handles)  = controlLeaf stmt
extractPaths' _ (stmt@(Assign {}), handles)  = controlLeaf stmt
extractPaths' _ (stmt@(AAssign {}), handles) = controlLeaf stmt
extractPaths' n (Block _ stmt, handles)      = extractPaths' n (handles $+> stmt)

extractPaths' n (IfThenElse cond thenStmt elseStmt, handles) =
  Bin cond thenPaths elsePaths
  where thenPaths = extractPaths' (n - 1) (handles $+> thenStmt)
        elsePaths = extractPaths' (n - 1) (handles $+> elseStmt)

extractPaths' n (while@(While cond body), handles) =
  Bin cond (extractPaths' (n - 1) (handles $+> body +: while)) Leaf

extractPaths' n (TryCatch _ try catch, handles) = extractPaths' n ((catch : handles) $+> try)

extractPaths' n (Seq (Block _ stmt1) stmt2, handles) = extractPaths' n (handles $+> (stmt1 +: stmt2))

-- append statements following an if-then-else to both branches
extractPaths' n (Seq (IfThenElse cond thenStmt elseStmt) stmt, handles) =
  Bin cond thenPaths elsePaths
    where thenPaths = extractPaths' (n - 1) (handles $+> thenStmt +: stmt)
          elsePaths = extractPaths' (n - 1) (handles $+> elseStmt +: stmt)

extractPaths' n (while@(Seq (While cond body) stmt), handles) =
  Bin cond whilePaths exitPaths
  where whilePaths = extractPaths' (n - 1) (handles $+> (body +: while))
        exitPaths  = extractPaths' (n - 1) (handles $+> stmt)

extractPaths' n (Seq (TryCatch _ try catch) stmt2, handles) =
  extractPaths' n ((catch : handles) $+> try +: stmt2)

extractPaths' n (Seq stmt1 stmt2, handles) = Uni stmt1 (extractPaths' (n - 1) (handles $+> stmt2))

extractPaths' _ _ = error "not yet implemented"

toMaybe :: Either l r -> Maybe r
toMaybe (Right r) = Just r
toMaybe (Left _)  = Nothing

testExtract :: Int -> String -> IO (Maybe ControlPath)
testExtract n file = do
  gcl <- parseGCLfile file
  return $ fmap (extractPaths n . stmt) (toMaybe gcl)
  -- return $ fmap (extractPaths 1000000 . stmt) (toMaybe gcl)

