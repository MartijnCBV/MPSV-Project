module Main where

import GCLParser.Parser ( parseGCLfile )
import Type (annotateForProgram)
import Tree.ProgramPath (extractPaths, listPaths)
import GCLParser.GCLDatatype

checkProgram :: (Integral n) => n -> String -> IO ()
checkProgram depth path = do
  gcl <- parseGCLfile path
  prgm <- case gcl of
    Left err -> error err
    Right prgm -> pure prgm
  let annotate = annotateForProgram prgm
  let paths = listPaths $ extractPaths depth (stmt prgm)

  return ()

main :: IO ()
main = putStrLn "Hello world"
