module Stats where

data Stats = Stats {
  nodes :: Int,
  paths :: Int,
  unfins :: Int,
  infeasibles:: Int
} deriving (Show)

type WithStats a = (a, Stats)

node :: Stats -> Stats
node stats@Stats {nodes=n} = stats{nodes=n + 1}
path :: Stats -> Stats
path stats@Stats {paths=n} = stats{paths=n + 1}
unfin :: Stats -> Stats
unfin stats@Stats {unfins=n} = stats{unfins=n + 1}
infeasible :: Stats -> Stats
infeasible stats@Stats {infeasibles=n} = stats{infeasibles=n + 1}

emptyStats :: Stats
emptyStats = Stats 0 1 0 0

(+++) :: Stats -> Stats -> Stats
(Stats nodes1 paths1 unfins1 infeasibles1) +++ (Stats nodes2 paths2 unfins2 infeasibles2) = 
  Stats (nodes1 + nodes2) (paths1 + paths2) (unfins1 + unfins2) (infeasibles1 + infeasibles2)
