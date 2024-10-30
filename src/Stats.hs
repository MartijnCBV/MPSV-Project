module Stats where

data Stats = Stats {
  nodes :: Int,
  unfins :: Int,
  infeasibles :: Int,
  totalSize :: Int
} deriving (Show)

type WithStats a = (a, Stats)

node :: Stats -> Stats
node stats@Stats {nodes=n} = stats{nodes=n + 1}
unfin :: Stats -> Stats
unfin stats@Stats {unfins=n} = stats{unfins=n + 1}
infeasible :: Stats -> Stats
infeasible stats@Stats {infeasibles=n} = stats{infeasibles=n + 1}

emptyStats :: Stats
emptyStats = Stats 0 0 0 0

(+++) :: Stats -> Stats -> Stats
(Stats nodes1 unfins1 infeasibles1 size1) +++ (Stats nodes2 unfins2 infeasibles2 size2) = 
  Stats (nodes1 + nodes2) (unfins1 + unfins2) (infeasibles1 + infeasibles2) (size1 + size2)
