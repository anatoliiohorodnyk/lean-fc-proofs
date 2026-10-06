# Independent check: triangle-free, chromatic number >= 4, f(G) <= 3, n <= 14

No reference number disagrees. All reference values (triangle-free counts for n = 11..14;
non-3-colourable counts 0 for n <= 10, 1 for n = 11, 24 for n = 12) were reproduced exactly.

## Verdict

**The claim holds.** No triangle-free graph on n <= 14 vertices has chromatic number >= 4 and f(G) <= 3.
Among all triangle-free non-3-colourable graphs on at most 14 vertices the minimum of f is 4
(reached at n = 13 and n = 14); for n <= 10 there are no such graphs at all.
The 15-vertex graph of step 5 is triangle-free, 4-chromatic and has f = 3, so the bound n <= 14 cannot be raised.

## Table (steps 1-3)

| n | triangle-free graphs (geng -t) | not 3-colourable | min f | distribution of f among the not-3-colourable graphs |
|---|---|---|---|---|
| 1 | 1 | 0 | - | - |
| 2 | 2 | 0 | - | - |
| 3 | 3 | 0 | - | - |
| 4 | 7 | 0 | - | - |
| 5 | 14 | 0 | - | - |
| 6 | 38 | 0 | - | - |
| 7 | 107 | 0 | - | - |
| 8 | 410 | 0 | - | - |
| 9 | 1897 | 0 | - | - |
| 10 | 12172 | 0 | - | - |
| 11 | 105071 | 1 | 5 | 5:1 |
| 12 | 1262180 | 24 | 5 | 5:8, 6:6, 7:2, 8:4, 10:3, 12:1 |
| 13 | 20797002 | 1110 | 4 | 4:60, 5:301, 6:227, 7:231, 8:114, 9:123, 10:32, 11:19, 12:2, 13:1 |
| 14 | 467871369 | 76261 | 4 | 4:3292, 5:17433, 6:21107, 7:15445, 8:11904, 9:4500, 10:2192, 11:285, 12:99, 13:3, 14:1 |

The claim holds for n when min f >= 4 (or when no graph is kept): true for every n = 1..14.
Examples with f = 4: `L??CAB_uAkB[iQ` (n = 13), `M???C@?wEoMGE[bh?` (n = 14).
Order of work was as required: generation, then colouring test on every graph, and f computed
only afterwards on the kept files. Every kept graph was also re-checked to be triangle-free (0 failures).

### n = 14 per part (geng res/mod, 4 parts on 4 cores)

| part | graphs generated | not 3-colourable | geng CPU time | wall time of pipeline | f = 4 count |
|---|---|---|---|---|---|
| 0/4 | 119811633 | 20292 | 166.58 s | 330 s | 1122 |
| 1/4 | 128077499 | 17440 | 180.02 s | 345 s | 796 |
| 2/4 | 125627412 | 18740 | 172.74 s | 338 s | 709 |
| 3/4 | 94354825 | 19789 | 140.49 s | 285 s | 665 |
| sum | 467871369 | 76261 | | | 3292 |

The 76261 kept graph6 strings are pairwise distinct. n = 13: one part, 20797002 graphs, 31 s wall
(geng 30.40 s). n <= 12: under 2 s each. Counts read by the filter equal geng's own ">Z" counts in every run.

## Step 4: validation of the colouring test

Main test `col3` (bitmask backtracking, branch on the vertex with fewest admissible colours, colour
symmetry breaking) against `brute3` (enumeration of all 3^n maps, separately written graph6 decoder):

| n | all graphs | not 3-colourable (brute) | not 3-colourable (col3) | mismatches |
|---|---|---|---|---|
| 1 | 1 | 0 | 0 | 0 |
| 2 | 2 | 0 | 0 | 0 |
| 3 | 4 | 0 | 0 | 0 |
| 4 | 11 | 1 | 1 | 0 |
| 5 | 34 | 5 | 5 | 0 |
| 6 | 156 | 37 | 37 | 0 |
| 7 | 1044 | 377 | 377 | 0 |
| 8 | 12346 | 6322 | 6322 | 0 |

Total: **13598 comparisons, 0 mismatches** (the sets of rejected graphs were compared, not only the counts).

Additional checks beyond what was asked:

- `brute3` on all triangle-free graphs with n = 9, 10 (1897 + 12172): all 3-colourable, agreeing with col3.
- `brute3` on the graphs kept by col3: all 1 (n = 11), 24 (n = 12), 1110 (n = 13) confirmed not
  3-colourable; for n = 14 a sample of 1526 (every 50th line) confirmed, 0 disagreements. The other
  n = 14 kept graphs were not brute-forced (would take about 3 hours).
- A third program `col3b` (adjacency matrix, fixed vertex order, and it re-verifies each colouring it
  finds against the edges) was run over the complete n = 13 and n = 14 generations a second time.
  Its output files are byte-identical to col3's for n = 13 and for each of the four n = 14 parts
  (1110 and 20292 / 17440 / 18740 / 19789 graphs). It verified an explicit proper 3-colouring for each
  of the other 20795892 + 467795108 graphs. So for n = 13, 14 no graph was wrongly discarded as
  3-colourable. It also gives 1 and 24 for n = 11, 12. Run time 437 s.

## Step 5: the 15-vertex graph

- 15 vertices, 30 edges, no repeated edge or loop.
- Triangle-free: yes (0 triangles among all 455 triples).
- Degrees by vertex 0..14: 5, 6, 4, 6, 5, 4, 3, 3, 4, 3, 6, 5, 2, 2, 2.
- Degree sequence: 6,6,6,5,5,5,4,4,4,3,3,3,2,2,2; each of the degrees 2..6 occurs exactly 3 times, so **f = 3**.
- Chromatic number **4**: not 3-colourable by exhaustive enumeration in Python (3^14 maps, vertex 0
  fixed), also by col3 and brute3 on its graph6 `NhdLA_gc?NqcQ??BI??`; proper 4-colouring
  (vertices 0..14): 0,1,0,1,2,0,1,0,1,2,3,2,0,0,0.

## Environment and exact commands

- nauty: Debian/Ubuntu package `nauty 2.8.8+ds-5`; `nauty-geng --version` prints "Nauty&Traces version 2.8081 (32 bits)".
  geng's own header for the n = 14 run: `>A nauty-geng -tX0x200d0D13 n=14 e=0-49 class=0/4`.
- gcc 13.3.0, `-O2`; 4 cores (QEMU virtual CPU, 2.0 GHz), 2 GB RAM. Nothing under the directories of the session that produced the claim was read.

```
gcc -O2 -Wall -o col3 src/col3.c ; gcc -O2 -Wall -o brute3 src/brute3.c ; gcc -O2 -Wall -o col3b src/col3b.c
# n = 1..12
nauty-geng -t $n 2>logs/geng_$n.err | ./col3 > out/not3col_$n.g6 2> logs/col3_$n.err
# n = 13 and n = 14, detached:  setsid nohup ./run_all.sh > logs/run_all.out 2>&1 < /dev/null &
nauty-geng -t 13 0/1 2>logs/geng_13_0of1.err | ./col3 > out/not3col_13_0of1.g6 2> logs/col3_13_0of1.err
nauty-geng -t 14 $r/4 2>logs/geng_14_${r}of4.err | ./col3 > out/not3col_14_${r}of4.g6 2> logs/col3_14_${r}of4.err   # r = 0,1,2,3 in parallel
# step 3
python3 src/fstat.py < out/not3col_$n.g6        # n = 14: cat of the four parts -> out/not3col_14.g6
# step 4
nauty-geng -q $n > out/all_$n.g6 ; ./brute3 < out/all_$n.g6 ; ./col3 < out/all_$n.g6   # n = 1..8, rejected sets compared with comm
# step 5
python3 src/step5.py
# second full pass:  ./run_b.sh   (nauty-geng -tq 13 | ./col3b ;  nauty-geng -tq 14 $r/4 | ./col3b)
```

Files: `src/` (col3.c, brute3.c, col3b.c, fstat.py, step5.py), `run_part.sh`, `run_all.sh`, `run_b.sh`,
`logs/` (geng and filter stderr per run), `out/` (kept graphs `not3col_*.g6`, step 5 output `step5.txt`).
