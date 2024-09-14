module Tree.ProgramPath where

import GCLParser.GCLDatatype
import GCLParser.Parser ( parseGCLfile )

orElse :: Maybe t -> Maybe t -> Maybe t
orElse val@(Just _) _   = val
orElse Nothing      def = def

data ControlPath = Basic Stmt (Maybe ControlPath)
  | Branch Expr ControlPath ControlPath
  deriving (Show)

(+:) :: Stmt -> Stmt -> Stmt
(Seq lstmt1 lstmt2) +: rstmt = 
  Seq lstmt1 (lstmt2 +: rstmt)
lstmt +: rstmt         = Seq lstmt rstmt

controlLeaf :: Stmt -> ControlPath
controlLeaf stmt = Basic stmt Nothing

extractPaths :: Stmt -> ControlPath
extractPaths stmt@Skip         = controlLeaf stmt
extractPaths stmt@(Assert {})  = controlLeaf stmt
extractPaths stmt@(Assume {})  = controlLeaf stmt
extractPaths stmt@(Assign {})  = controlLeaf stmt
extractPaths stmt@(AAssign {}) = controlLeaf stmt
extractPaths (Block _ stmt)    = extractPaths stmt

-- append statements following an if-then-else to both branches
extractPaths (Seq (IfThenElse cond thenStmt elseStmt) stmt) =
  Branch cond thenPaths elsePaths
    where thenPaths = extractPaths $ thenStmt +: stmt
          elsePaths = extractPaths $ elseStmt +: stmt

extractPaths (Seq stmt1 stmt2) = Basic stmt1 (Just $ extractPaths stmt2)
extractPaths (IfThenElse cond thenStmt elseStmt) = Branch cond (extractPaths thenStmt) (extractPaths elseStmt)

extractPaths _ = error "not yet implemented"
-- extractPaths (While cond body) = Branch cond thenStmt elseStmt

toMaybe :: Either l r -> Maybe r
toMaybe (Right r) = Just r
toMaybe (Left _)  = Nothing

testExtract :: String -> IO (Maybe ControlPath)
testExtract file = do
  gcl <- parseGCLfile file
  return $ fmap (extractPaths . stmt) (toMaybe gcl)

