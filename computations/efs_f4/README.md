# Computations for "the smallest counterexample to Graffiti's Conjecture 67 has 15 vertices"

Nothing in this directory is part of a Lean proof. It documents the exhaustive search behind
F(4) ≥ 15 and the searches that found the graphs.

f(G) = the largest number of vertices of G having the same degree. Claim checked here: no
triangle-free graph on n ≤ 14 vertices has chromatic number ≥ 4 and f ≤ 3; and every
triangle-free graph on n ≤ 14 vertices with f ≤ 2 is bipartite. Graphs need not be connected and
may have isolated vertices.

Tools: nauty 2.8.8 (Debian package `nauty 2.8.8+ds-5`; `nauty-geng --version` prints
"Nauty&Traces version 2.8081 (32 bits)"), gcc 13.3.0 `-O2`, Python 3.12 with networkx 3.7
(only for the small scripts). Machine: 4 cores, 2 GB RAM.

## Layout

| path | content |
|---|---|
| `search/` | the first run and the graph searches (programs of the session that produced the claim) |
| `independent_run/` | the second run: sources, scripts, logs, outputs and report of a separate agent that was given only the claim. Its files are unchanged except for the two path edits listed at the end |
| `graphs/` | all triangle-free graphs that are not 3-colourable, n = 11, 12, 13, 14, in graph6, one per isomorphism class, as produced by the independent run |

## Expected counts

| n | triangle-free graphs (`nauty-geng -t n`) | not 3-colourable | of these with f ≤ 3 | with f ≤ 2 | of these not bipartite |
|---|---|---|---|---|---|
| 1–10 | 1, 2, 3, 7, 14, 38, 107, 410, 1897, 12172 | 0 | 0 | 1, 2, 2, 3, 2, 3, 4, 7, 5, 9 | 0 |
| 11 | 105071 | 1 | 0 | 13 | 0 |
| 12 | 1262180 | 24 | 0 | 23 | 0 |
| 13 | 20797002 | 1110 | 0 | 17 | 0 |
| 14 | 467871369 | 76261 | 0 | 46 | 0 |

n = 14 by part `r/4`, r = 0..3: 119811633, 128077499, 125627412, 94354825 graphs; not
3-colourable 20292, 17440, 18740, 19789; with f ≤ 3 (first run) 590741, 969930, 914352, 532562;
with f ≤ 2: 7, 10, 14, 15.

Graphs with f ≤ 3 (first run), n = 11..14: 6768, 48129, 304993, 3007585.

`graphs/` (sha256):

    a4e71c333c3fdf6c571e6ffde758254ec63b6b89647779aa76ff9257cdd5d3ac  trianglefree_not3colourable_n11.g6   (1 graph)
    5c72807a3a8879f6cc087d758d1acbe80d0bd4b17d741f483264eec1f11afc7b  trianglefree_not3colourable_n12.g6   (24)
    e80178ce36728107cdc0dbc2183f3c648156c7fdb50faa86917bc99114a10f3a  trianglefree_not3colourable_n13.g6   (1110)
    4975290f8ba25c6cbaadf31621dcd13d8e54e464a0b3eddd82603de546eba1be  trianglefree_not3colourable_n14.g6   (76261)

These are copies of `independent_run/out/not3col_11.g6`, `not3col_12.g6`, `not3col_13_0of1.g6`
and `not3col_14.g6`. For n = 11, 12, 13 the first run produces the same sets (compared after
sorting). The first run did not produce the list for n = 14 (it applied the degree condition
first), so that list comes from the independent run only; there it was produced twice, by two
different solvers, with identical output.

## First run (`search/`)

    gcc -O2 -o efs_filter efs_filter.c
    # claim: f <= 3 first, then the 3-colouring test; prints the graphs that fail it (none)
    nauty-geng -q -t $n | ./efs_filter 4 3          # n = 11, 12, 13
    nauty-geng -q -t 14 $r/4 | ./efs_filter 4 3     # r = 0, 1, 2, 3 in parallel
    # without the degree condition (counts 1, 24, 1110 for n = 11, 12, 13; 0 for n <= 10)
    nauty-geng -q -t $n | ./efs_filter 4 99         # n = 1..13
    # f <= 2 implies bipartite: f <= 2 first, then the 2-colouring test
    nauty-geng -q -t $n | ./efs_filter 3 2          # n = 1..13
    nauty-geng -q -t 14 $r/4 | ./efs_filter 3 2     # r = 0, 1, 2, 3

`efs_filter k fmax` reads graph6, skips graphs with f > fmax, re-checks triangle-freeness, and
prints the graphs that are not (k−1)-colourable (plain backtracking in vertex order, colours
used in increasing order). Counts go to stderr; `logs/` has the stderr of the n = 14 runs
(`chi4_14_r.log` for the claim, `f2_14_r.log` for f ≤ 2). Run times: n = 13 about 35 s on one core; the n = 14
runs were not timed exactly (the independent run measured 285–345 s per part with its own program).

Other files:

| file | purpose |
|---|---|
| `efs_anneal.py n` | local search for a triangle-free supergraph of the Grötzsch graph on n vertices with f ≤ 3; found the 15-vertex graph (`efs_anneal.py 15`, first seed) |
| `efs_verify15.py` | independent check of the 15-vertex graph |
| `efs_paper19.py` | the 19-vertex graph of the 1991 paper, built from its description: 48 edges, triangle-free, degrees 2² 3³ 4³ 5³ 6³ 7² 8³, f = 3, chromatic number 4 |
| `efs_thm1.py` | test of Theorem 1 of the paper on connected triangle-free graphs up to 11 vertices |
| `efs_anneal5.py n`, `f5_n34_edges.txt` | search for F(5) from the Mycielskian of the Grötzsch graph, and the 34-vertex graph found (search result only) |

## Independent run (`independent_run/`)

See `independent_run/REPORT.md`, which lists its commands. Sources: `src/col3.c` (main
3-colouring test), `src/brute3.c` (all 3^n maps), `src/col3b.c` (second solver), `src/fstat.py`
(f of the kept graphs), `src/step5.py` (the 15-vertex graph). Scripts `run_part.sh`,
`run_all.sh`, `run_b.sh`; `logs/` and `out/` are the logs and outputs of the run as they were.
The compiled binaries are not included; build them with the `gcc` line of the report.

Changes made to the independent run's files for publication (nothing else was edited):

1. `run_part.sh`, `run_all.sh`, `run_b.sh`: the line `cd <absolute directory of the run>` was
   replaced by `cd "$(dirname "$0")"`.
2. `REPORT.md`, environment section: the two absolute directory names of the other session in
   the sentence "Nothing under … was read" were replaced by a description.

Both runs use the same generator (`nauty-geng`, same package). An error in the generator would
not be detected by comparing them.
