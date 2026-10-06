#!/bin/sh
# usage: run_part.sh n res mod
n=$1; r=$2; m=$3
cd "$(dirname "$0")"
tag=${n}_${r}of${m}
s=$(date +%s)
nauty-geng -t $n $r/$m 2>logs/geng_$tag.err | ./col3 > out/not3col_$tag.g6 2> logs/col3_$tag.err
echo "geng_exit_and_pipe_done elapsed=$(( $(date +%s) - s ))s" > logs/done_$tag
