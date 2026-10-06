#!/bin/sh
cd "$(dirname "$0")"
s=$(date +%s)
nauty-geng -tq 13 | ./col3b > out/b_not3col_13.g6 2> logs/col3b_13.err
for r in 0 1 2 3; do (nauty-geng -tq 14 $r/4 | ./col3b > out/b_not3col_14_${r}of4.g6 2> logs/col3b_14_${r}of4.err) & done
wait
echo "elapsed=$(( $(date +%s) - s ))s" > logs/BDONE
