module Predicate.Tactics where

import Z3.Monad
import Z3.Base (Tactic)

mkTactics :: [String] -> Z3 Tactic
mkTactics []     = error "empty tactic is not possible"
mkTactics [n]    = mkTactic n
mkTactics (n:ns) = do
  t1 <- mkTactic n
  ts <- mkTactics ns
  andThenTactic t1 ts

chain :: Z3 Tactic
chain = mkTactics ["simplify"
                  , "propagate-ineqs"
                  , "propagate-values"
                  , "bit-blast"
                  , "qe"
                  , "simplify"
                  , "ackermannize_bv"
                  , "ctx-simplify"
                  , "lia2pb"
                  , "normalize-bounds"
                  , "smt"
                  ]