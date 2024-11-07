{-# LANGUAGE LambdaCase #-}
module Config where

import Tree.Heuristic
import Options.Applicative

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

parseHeuristic :: ReadM (Int -> Heuristic)
parseHeuristic = eitherReader $ \case
  "never"     -> Right $ const never
  "always"    -> Right $ const checkAll
  "second"    -> Right $ \_ -> linear 2 Depth
  "expSecond" -> Right $ \_ -> exponential 2 Depth
  "half"      -> Right $ \d -> untilDepth (d `div` 2) Depth checkAll
  s           -> Left $ "Unsupported heuristic: " ++ s

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
