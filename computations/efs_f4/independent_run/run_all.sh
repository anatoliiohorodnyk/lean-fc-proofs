#!/bin/sh
cd "$(dirname "$0")"
./run_part.sh 13 0 1
for r in 0 1 2 3; do ./run_part.sh 14 $r 4 & done
wait
echo ALLDONE > logs/ALLDONE
