module Stats where

data Stats = Stats {
  nodes :: Int,
  unfins :: Int,
  feasChecks :: Int,
  infeasibles :: Int,
  feasSize :: Int,
  validSize :: Int
} deriving (Show)

type WithStats a = (a, Stats)

node :: Stats -> Stats
node stats@Stats {nodes=n} = stats{nodes=n + 1}
unfin :: Stats -> Stats
unfin stats@Stats {unfins=n} = stats{unfins=n + 1}
feasCheck :: Stats -> Stats
feasCheck stats@Stats {feasChecks=n} = stats{feasChecks=n + 1}
feasCheck2 :: Stats -> Stats
feasCheck2 stats@Stats {feasChecks=n} = stats{feasChecks=n + 2}
infeasible :: Stats -> Stats
infeasible stats@Stats {infeasibles=n} = stats{infeasibles=n + 1}
addSize :: Int -> Stats -> Stats
addSize m stats@Stats {feasSize=n} = stats{feasSize=n+m}

emptyStats :: Stats
emptyStats = Stats 0 0 0 0 0 0

(+++) :: Stats -> Stats -> Stats
(Stats nodes1 unfins1 feasChecks1 infeasibles1 fSize1 vSize1) +++ (Stats nodes2 unfins2 feasChecks2 infeasibles2 fSize2 vSize2) = 
  Stats (nodes1 + nodes2) (unfins1 + unfins2) (feasChecks1 + feasChecks2) (infeasibles1 + infeasibles2) (fSize1 + fSize2) (vSize1 + vSize2)
