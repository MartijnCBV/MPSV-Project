{-# LANGUAGE InstanceSigs #-}
module Tree.ProgramPath where

import GCLParser.GCLDatatype
import GCLParser.Parser ( parseGCLfile )
import Data.Foldable
import Data.Bits

data UniBinTree u b = Leaf
  | Uni u (UniBinTree u b)
  | Bin b (UniBinTree u b) (UniBinTree u b)

type ControlPath = UniBinTree Stmt Expr

instance (Show u, Show b) => Show (UniBinTree u b) where
  -- show :: UniBinTree u b -> String
  -- show = printTree 0
  show x = "digraph {" ++ printTreeDot x ++ "}"

printTree :: (Show u, Show b) => Int -> UniBinTree u b -> String
printTree n Leaf               = replicate (n * 2) ' ' ++ "Leaf\n"
printTree n (Uni u next)       = replicate (n * 2) ' ' ++ show u ++ "\n" ++ printTree n next
printTree n (Bin b left right) = replicate (n * 2) ' ' ++ show b ++ "\n" ++ indent ++ "< LEFT >\n" ++ printTree (n + 1) left ++ indent ++ "< RIGHT >\n" ++ printTree (n + 1) right
  where indent = replicate ((n + 1) * 2) ' '

printTreeDot :: (Show u, Show b) => UniBinTree u b -> String
printTreeDot t = let i = 0 in printTreeDot' i t ++ printTreeDot'' i t

printTreeDot' :: (Show u, Show b) => Int -> UniBinTree u b -> String
printTreeDot' _ Leaf               = ""
printTreeDot' i (Uni u next)       = printValueDotLabel i u ++ "\n" ++ printTreeDot' (i + 1) next
printTreeDot' i (Bin b left right) = printValueDotLabel i b ++ "\n" ++ printTreeDot' (i + 1) left ++ printTreeDot' (i + 1) right

printTreeDot'' :: (Show u, Show b) => Int -> UniBinTree u b -> String
printTreeDot'' _ Leaf               = ""
printTreeDot'' i (Uni u next)       = printTreeNextVal i u next ++ printTreeDot'' (i + 1) next
printTreeDot'' i (Bin b left right) = printTreeNextVal i b left 
                                   ++ printTreeNextVal i b  right 
                                   ++ printTreeDot'' (i + 1) left 
                                   ++ printTreeDot'' (i + 1) right

printTreeNextVal :: (Show v, Show u, Show b) => Int -> v -> UniBinTree u b -> String
printTreeNextVal i v x | s /= ""   = printValueDot i v ++ " -> " ++ s ++ "\n"
                       | otherwise = ""
  where 
    f x' = case x' of
      Leaf      -> ""
      Uni y _   -> printValueDot (i + 1) y
      Bin y _ _ -> printValueDot (i + 1) y
    s = f x 

printValueDotLabel :: Show u => Int -> u -> String
printValueDotLabel i x = printValueDot i x ++ "[label=\"" ++ show x ++ "\"]"

printValueDot :: Show u => Int -> u -> String
printValueDot i x = show (i + djb2 (show x))

djb2 :: String -> Int
djb2 = foldl' (\h c -> 33*h `xor` fromEnum c) 5381

orElse :: Maybe t -> Maybe t -> Maybe t
orElse val@(Just _) _   = val
orElse Nothing      def = def

-- data ControlPath = Basic Stmt (Maybe ControlPath)
--   | Branch Expr ControlPath ControlPath
--   deriving (Show)

(+:) :: Stmt -> Stmt -> Stmt
(Seq lstmt1 lstmt2) +: rstmt =
  Seq lstmt1 (lstmt2 +: rstmt)
lstmt +: rstmt         = Seq lstmt rstmt

controlLeaf :: Stmt -> ControlPath
controlLeaf stmt = Uni stmt Leaf

extractPaths :: Int -> Stmt -> ControlPath
extractPaths 0 _                 = Leaf
extractPaths _ stmt@Skip         = controlLeaf stmt
extractPaths _ stmt@(Assert {})  = controlLeaf stmt
extractPaths _ stmt@(Assume {})  = controlLeaf stmt
extractPaths _ stmt@(Assign {})  = controlLeaf stmt
extractPaths _ stmt@(AAssign {}) = controlLeaf stmt
extractPaths n (Block _ stmt)    = extractPaths n stmt

extractPaths n (IfThenElse cond thenStmt elseStmt) =
  Bin cond (extractPaths (n - 1) thenStmt) (extractPaths (n - 1) elseStmt)
extractPaths n (While cond body) = Bin cond (extractPaths (n - 1) body) Leaf

extractPaths n (Seq (Block _ stmt1) stmt2) = extractPaths n (stmt1 +: stmt2)

-- append statements following an if-then-else to both branches
extractPaths n (Seq (IfThenElse cond thenStmt elseStmt) stmt) =
  Bin cond thenPaths elsePaths
    where thenPaths = extractPaths (n - 1) (thenStmt +: stmt)
          elsePaths = extractPaths (n - 1) (elseStmt +: stmt)

extractPaths n (Seq while@(While cond body) stmt) = Bin cond whilePaths exitPaths
  where whilePaths = extractPaths (n - 1) (body +: while)
        exitPaths  = extractPaths (n - 1) stmt

extractPaths n (Seq stmt1 stmt2) = Uni stmt1 (extractPaths (n - 1) stmt2)

extractPaths _ _ = error "not yet implemented"
-- extractPaths (While cond body) = Branch cond thenStmt elseStmt

toMaybe :: Either l r -> Maybe r
toMaybe (Right r) = Just r
toMaybe (Left _)  = Nothing

testExtract :: Int -> String -> IO (Maybe ControlPath)
testExtract n file = do
  gcl <- parseGCLfile file
  return $ fmap (extractPaths n . stmt) (toMaybe gcl)
  -- return $ fmap (extractPaths 1000000 . stmt) (toMaybe gcl)

