#!/bin/bash

touch res
echo "Verifying file $1 with depth $2 and heuristic $3"
echo $3 >> res
for i in {1..5}; do
  echo "Run $i"
  cabal run exes -- $1 --csv -d $2 -h $3 >> res
done
echo "Done"

