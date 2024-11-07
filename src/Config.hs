{-# LANGUAGE LambdaCase #-}
module Config where

import Tree.Heuristic
import Options.Applicative
import Data.Char (isDigit)
import Text.Read (readMaybe)

data Config = Config {
  file :: String,
  depth :: Int,
  heuristic :: Heuristic,
  findExcept :: Bool,
  optPruning :: Bool,
  optFormulas :: Bool,
  csv :: Bool,
  showPath :: Bool
}

splitOn :: (Char -> Bool) -> String -> [String]
splitOn p s =  case dropWhile p s of
                      "" -> []
                      s' -> w : splitOn p s''
                            where (w, s'') = break p s'

tryRead :: (Read n) => String -> Either String n
tryRead text = case readMaybe text of
  Nothing  -> Left $ "Not a number: " ++ text
  Just num -> Right num

parseParamHeuristic :: String -> Either String (Int -> Heuristic)
parseParamHeuristic text = case break isDigit text of
  ("lin", s) -> do num <- tryRead s; Right $ \_ -> linear num Depth
  ("exp", s) -> do num <- tryRead s; Right $ \_ -> exponential num Depth
  ("linB", s) -> do num <- tryRead s; Right $ \_ -> linear num Branches
  ("expB", s) -> do num <- tryRead s; Right $ \_ -> exponential num Branches
  ("minConj", s) -> do num <- tryRead s; Right $ \_ -> minConjunctions num
  ("minSize", s) -> do num <- tryRead s; Right $ \_ -> minSize num
  ("maxSize", s) -> do num <- tryRead s; Right $ \_ -> maxSize num
  _ -> Left $ "Unsupported heuristic: " ++ text

parseHeuristic :: ReadM (Int -> Heuristic)
parseHeuristic = eitherReader $ \case
  "never"       -> Right $ const never
  "always"      -> Right $ const checkAll
  "alwaysHalf"  -> Right $ \d -> untilDepth (d `div` 2) Depth checkAll
  "alwaysHalfB" -> Right $ \d -> untilDepth (d `div` 2) Branches checkAll
  "expHalf"     -> Right $ \d -> switchDepth (d `div` 2) Depth checkAll (exponential 2 Depth)
  "expHalfB"    -> Right $ \d -> switchDepth (d `div` 2) Branches checkAll (exponential 2 Depth)
  "linHalf"     -> Right $ \d -> switchDepth (d `div` 2) Depth (linear 2 Branches) (exponential 2 Depth)
  "linHalfB"    -> Right $ \d -> switchDepth (d `div` 2) Branches (linear 2 Branches) (exponential 2 Depth)
  "thirds"      -> Right $ \d -> switchDepth (d `div` 3) Depth checkAll (switchDepth ((d `div` 3) * 2) Depth (linear 2 Branches) (exponential 2 Depth))
  "thirdsB"     -> Right $ \d -> switchDepth (d `div` 3) Branches checkAll (switchDepth ((d `div` 3) * 2) Branches (linear 2 Branches) (exponential 2 Depth))
  s             -> parseParamHeuristic s

mkConfig :: String -> Int -> (Int -> Heuristic) -> Bool -> Bool -> Bool -> Bool -> Bool -> Config
mkConfig f d mkH = Config f d (mkH d)

config :: Parser Config
config = mkConfig
      <$> argument str
          ( metavar "FILE"
         <> help "File to verify" )
      <*> option auto
          ( long "depth"
         <> short 'd'
         <> help "Depth to verify to"
         <> showDefault
         <> value 10
         <> metavar "INT" )
      <*> option parseHeuristic
          ( long "heur"
         <> short 'h'
         <> help "Branch pruning heuristic to use"
         <> value (const checkAll)
         <> metavar "NAME")
      <*> switch
          ( long "find-except"
         <> short 'e'
         <> help "Find branches that terminate exceptionally")
      <*> switch
          ( long "opt-branch"
         <> help "Optimize branch pruning")
      <*> switch
          ( long "opt-formula"
         <> help "Optimize formulas before passing to Z3")
      <*> switch
          ( long "csv"
         <> help "Print in CSV format")
      <*> switch
          ( long "path"
         <> short 'p'
         <> help "Show counterexample's path")
