module Main where
import GCLParser.GCLDatatype
import Tree.ProgramPath
import Test.HUnit
import qualified System.Exit as Exit

{-
x := 10;
y := 5
-}
true :: Expr
true = LitB True

lit10 :: Expr
lit10 = LitI 10

lit5 :: Expr
lit5 = LitI 5

varX :: Expr
varX = Var "x"

simpleProg :: Stmt
simpleProg = Seq (Assign "x" lit10) (Assign "y" lit5)

branchingProg :: Stmt
branchingProg = Seq (IfThenElse true simpleProg (Assign "y" varX)) (Assign "z" true)

loopingProg :: Stmt
loopingProg = Seq (While true (Assign "y" varX)) (Assign "z" true)

testPrepend :: Test
testPrepend =
  TestCase (assertEqual "prepend adds left-sequentially"
    (Seq (Assign "x" lit10)
      (Seq (Assign "y" lit5)
        (Seq (Assign "x" lit10) (Assign "y" lit5))))
    (simpleProg +: simpleProg)
  )

testExtractLength0 :: Test
testExtractLength0 =
  TestCase (assertEqual "extract 0 gives leaf"
  Leaf
  (extractPaths 0 simpleProg))

testExtractLength1 :: Test
testExtractLength1 =
  TestCase (assertEqual "extract 1 gives single statement"
  (Uni (Assign "x" lit10) Leaf)
  (extractPaths 1 simpleProg))

testExtractLength2 :: Test
testExtractLength2 =
  TestCase (assertEqual "extract 2 gives full program"
  (Uni (Assign "x" lit10) 
    (Uni (Assign "y" lit5) Leaf))
  (extractPaths 2 simpleProg))

testExtractLength3 :: Test
testExtractLength3 =
  TestCase (assertEqual "extract 3 gives full program"
  (Uni (Assign "x" lit10) 
    (Uni (Assign "y" lit5) Leaf))
  (extractPaths 3 simpleProg))

testIfExtract :: Test
testIfExtract =
  TestCase (assertEqual "extract if gives branch"
  (Bin true
    (Uni (Assign "x" lit10)
      (Uni (Assign "y" lit5)
        (Uni (Assign "z" true) Leaf)
      )
    )
    (Uni (Assign "y" varX)
      (Uni (Assign "z" true) Leaf)
    )
  )
  (extractPaths 10 branchingProg))

testWhileExtract :: Test
testWhileExtract =
  TestCase (assertEqual "extract while keeps branching"
  (Bin true
    (Uni (Assign "y" varX)
      (Bin true
        (Uni (Assign "y" varX)
          (Bin true 
            (Uni (Assign "y" varX) Leaf)
            (Uni (Assign "z" true) Leaf)
          )
        )
        (Uni (Assign "z" true) Leaf)
      )
    )
    (Uni (Assign "z" true) Leaf)
  )
  (extractPaths 6 loopingProg))

testErrorsOn :: Test
testErrorsOn = TestList [
  TestCase (assertEqual "division throws"
    (Just $ opEqual varX zero)
    (errorsOn $ opDivide lit10 varX)
  ),
  TestCase (
    assertEqual "array access throws"
    (Just $ opOr (opLessThan varX zero) (opGreaterThanEqual varX (SizeOf (Var "a"))))
    (errorsOn $ ArrayElem (Var "a") varX)
  )
  ]

-- TODO: write unit tests for try-catch

tests :: Test
tests = TestList [
  TestLabel "prepend" testPrepend,
  TestLabel "length 0" testExtractLength0,
  TestLabel "length 1" testExtractLength1,
  TestLabel "length 2" testExtractLength2,
  TestLabel "length 3" testExtractLength3,
  TestLabel "test if" testIfExtract,
  TestLabel "test while" testWhileExtract,
  TestLabel "errors-on collection" testErrorsOn
  ]
 
main :: IO ()
main = do
    result <- runTestTT tests
    if failures result > 0 then Exit.exitFailure else Exit.exitSuccess