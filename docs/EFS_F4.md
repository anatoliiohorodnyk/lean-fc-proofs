# The smallest counterexample to Graffiti's Conjecture 67 has 15 vertices

## 1. Summary

Graffiti's Conjecture 67 (Written on the Wall, February 1987) says that the chromatic number of a
triangle-free graph does not exceed the largest number of occurrences of a degree. Erdős,
Fajtlowicz and Staton [EFS] disproved it and gave a counterexample on 19 vertices, the smallest
they knew.

**The smallest counterexample has exactly 15 vertices. Equivalently F(4) = 15, improving
F(4) ≤ 19.**

- The 15-vertex graph and the bound F(4) ≤ 15 are checked by the Lean kernel (Section 3).
- That nothing smaller exists is an exhaustive computer search, **not formalized**
  (Sections 4 and 5).
- F(3) = 7, the paper's value, is checked by the Lean kernel in both directions.

To our knowledge the exact value has not been stated before.

| statement | status |
|---|---|
| F(4) ≤ 15, hence F(4) ≤ 19 | Lean kernel; comparator for `F_four_le` |
| F(3) = 7 | Lean kernel; comparator |
| F(4) ≥ 15 | exhaustive computation, two independent runs, same graph generator |
| no counterexample to Conjecture 67 on at most 14 vertices | the same computation; one more run for f ≤ 2 (single run); one cited result (22 vertices for chromatic number 5) |
| F(5) ≤ 34 | search only (Section 7) |

Files of this repository:

| file | content | sha256 |
|---|---|---|
| `Proofs/T_SimpleGraph_F_four_le.lean` | `SimpleGraph.F_four_le_fifteen : F 4 ≤ 15` (L464) and `SimpleGraph.F_four_le : F 4 ≤ 19` (L469) | `ef6f07150c21a81a5ecf7ce4464743c1e15aa97a7c7a205ec3434fe5d65153ef` |
| `Proofs/T_SimpleGraph_F_three.lean` | `SimpleGraph.F_three : F 3 = 7` (L569) | `77624d3f4d6f982709ca6649ee74582bf86e2b04350dc8921d940666886c1b22` |
| `computations/efs_f4/` | programs, logs and graph lists of the search (not part of any proof) | see its README |

## 2. Definitions, the paper, prior work

For a finite simple graph G let f(G) be the largest number of vertices having the same degree
(`degreeSequenceMultiplicity` in formal-conjectures). The paper [EFS] proves that a
triangle-free graph with f ≤ 2 is bipartite (Theorem 1) and that every triangle-free graph is an
induced subgraph of a triangle-free graph with f = 3. It defines F(n) as the smallest p such
that some triangle-free graph on p vertices has chromatic number n and f = 3, shows F(3) = 7, and
shows F(4) ≤ 19 by a construction from the Grötzsch graph: a vertex of degree 2 on two
non-adjacent vertices of degree 4; three vertices each joined to the five vertices of degree 3;
three more each joined to those three; a last vertex of degree 2 on two non-adjacent vertices of
degree 6. We rebuilt this graph from the description: 19 vertices, 48 edges, triangle-free,
degree sequence 2² 3³ 4³ 5³ 6³ 7² 8³, f = 3, chromatic number 4
(`computations/efs_f4/search/efs_paper19.py`). No lower bound for F(4) is given, and the paper
ends by calling this graph the smallest counterexample to Conjecture 67 known to its authors.

**Isolated vertices.** The paper assumes graphs without isolated vertices. The definition of `F`
in formal-conjectures and the computation below allow them, and disconnected graphs in general.
The search found nothing on at most 14 vertices with isolated vertices allowed, and the
15-vertex graph has none (minimum degree 2), so the result holds under either convention.

**Prior computational work.** Brewster, Dinneen and Faber [BDF] tested about 200 conjectures of
Graffiti on all graphs with at most 10 vertices. Conjecture 67 does not appear among the
conjecture numbers named in their paper (it names the conjectures for which it gives
counterexamples or proofs); whether 67 was among those tested cannot be seen from the text. A
test up to 10 vertices could not have refuted it: there is no counterexample below 15 vertices.
Fajtlowicz's own *Written on the Wall* notes were not checked. Of the papers citing [EFS], those
we could open use only Theorem 1 or cite the paper generally; three were not opened
(Erdős–Faudree–Reid–Schelp 1995, Bollobás 1996, Sun–Hou–Zeng 2023).

## 3. The 15-vertex graph and its Lean certificate

30 edges:

    (0,1),(0,4),(0,6),(0,9),(0,11),(1,2),(1,5),(1,7),(1,12),(1,14),(2,3),(2,6),(2,8),(3,4),
    (3,7),(3,9),(3,11),(3,14),(4,5),(4,8),(4,12),(5,10),(5,11),(6,10),(7,10),(8,10),(8,11),
    (9,10),(10,13),(11,13)

graph6 in the same labelling: `NhdLA_gc?NqcQ??BI??`.

- Degrees of the vertices 0..14: 5, 6, 4, 6, 5, 4, 3, 3, 4, 3, 6, 5, 2, 2, 2. Each of 2, 3, 4,
  5, 6 occurs exactly three times, so f = 3.
- Triangle-free.
- A proper 4-colouring: 0, 1, 0, 1, 2, 0, 1, 0, 1, 2, 3, 2, 0, 0, 0.
- Not 3-colourable: the vertices 0..10 carry the Grötzsch graph (0–1–2–3–4 is a 5-cycle,
  5 + i is adjacent to i − 1 and i + 1 mod 5, and 10 is adjacent to 5, …, 9).

So χ = 4 > 3 = f. The graph was found by a local search over triangle-free supergraphs of the
Grötzsch graph with four extra vertices (`computations/efs_f4/search/efs_anneal.py`).

**Lean.** `Proofs/T_SimpleGraph_F_four_le.lean` is a copy of
`FormalConjectures/Paper/DegreeSequencesTriangleFree.lean` with about 150 lines of helper
declarations and the target proof. `efsG` is the graph above, given by a Boolean adjacency
function. `efs_cliqueFree` and `efs_colorable` are decided by kernel evaluation.
`efs_not_colorable` passes any 3-colouring through `efsNo3`, a Boolean search over the
colourings of the Grötzsch subgraph which the kernel evaluates to `true`. `efs_degSeq`
evaluates the degrees and identifies the sorted degree sequence. `F_four_le_fifteen` is
`Nat.sInf_le` applied to this witness, and `F_four_le` follows from it.

`Proofs/T_SimpleGraph_F_three.lean` (about 300 added lines). Upper bound: `efs3G`, a 5-cycle
0–1–2–3–4 with a vertex 5 adjacent to 1 and 3 and a vertex 6 adjacent to 5 (degrees
2,3,2,3,2,3,1), same scheme. Lower bound: `efs3_check` evaluates in the kernel an enumeration of
all graphs on 0 to 6 vertices: the pairs i < j are decided one after the other, a branch is cut
when the new edge closes a triangle, and every leaf has a proper 2-colouring or a degree
occurring at least four times. `efs3All_sound` and `efs3_small` turn this into: no triangle-free
graph on fewer than 7 vertices that is not 2-colourable has every degree occurring at most three
times.

Each file proves one target; the other statements of the copied file stay `sorry` (the library
is built with `warn.sorry = false`).

**Versions** (from the judge records of the two targets): formal-conjectures at
`df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1`, toolchain `leanprover/lean4:v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` (the revision in the `lake-manifest.json` of that
commit). The statement file has not changed between that commit and `76b8ea4e`.

**Checks.** `leanprover/comparator` accepts `F_three` and `F_four_le` against the repository
statements. `F_four_le_fifteen` is not a statement of formal-conjectures at that commit, so the
comparator does not cover it; it is the lemma from which `F_four_le` is derived in the file.
Axioms of both targets: `propext`, `Classical.choice`, `Quot.sound`. No `native_decide`; the
computations are `decide +kernel`.

**Building.**

    lake exe cache get
    lake build Proofs.T_SimpleGraph_F_four_le
    lake build Proofs.T_SimpleGraph_F_three

| file | wall time | peak memory |
|---|---|---|
| `T_SimpleGraph_F_four_le` | about 10 s | 1.3 GB |
| `T_SimpleGraph_F_three` | about 3.5 min | **17.3 GB** |

`F_three` needs a machine with more than 17 GB of memory. Almost all of it is the single
kernel evaluation `efs3_check` (the case of 6 vertices). It has not been optimised.

## 4. Why 15 is the smallest counterexample

A counterexample is a triangle-free graph G with χ(G) > f(G). Let G be one on n ≤ 14 vertices.

- χ(G) ≥ 5 is impossible: a triangle-free 5-chromatic graph has at least 22 vertices (Jensen and
  Royle [JR], as quoted in [G]).
- χ(G) = 4 needs f(G) ≤ 3: excluded for n ≤ 14 by the computation of Section 5.
- χ(G) = 3 needs f(G) ≤ 2. By Theorem 1 of [EFS] such a graph is bipartite. Independently of
  that theorem, every triangle-free graph on at most 14 vertices with f ≤ 2 is bipartite
  (Section 5).
- χ(G) = 2 needs f(G) ≤ 1, i.e. all degrees distinct, which is impossible for a graph with at
  least two vertices. χ(G) = 1 needs f(G) ≤ 0, which is impossible.

## 5. The computation (not formalized)

Claim: no triangle-free graph on n ≤ 14 vertices has chromatic number ≥ 4 and f ≤ 3. (The
definition of F asks for f = 3; excluding f ≤ 3 is stronger. Nothing is claimed for n ≥ 16.)

All triangle-free graphs were generated up to isomorphism with `nauty-geng -t n` (nauty 2.8.8;
no connectivity option, so disconnected graphs are included), n = 14 in four parts `r/4`.

| n | triangle-free graphs | not 3-colourable | minimum f among these | distribution of f among these |
|---|---|---|---|---|
| 1–10 | 1, 2, 3, 7, 14, 38, 107, 410, 1897, 12172 | 0 | – | – |
| 11 | 105 071 | 1 | 5 | 5:1 |
| 12 | 1 262 180 | 24 | 5 | 5:8, 6:6, 7:2, 8:4, 10:3, 12:1 |
| 13 | 20 797 002 | 1 110 | 4 | 4:60, 5:301, 6:227, 7:231, 8:114, 9:123, 10:32, 11:19, 12:2, 13:1 |
| 14 | 467 871 369 | 76 261 | 4 | 4:3292, 5:17433, 6:21107, 7:15445, 8:11904, 9:4500, 10:2192, 11:285, 12:99, 13:3, 14:1 |

Two runs with separately written programs, by two agents that did not share files:

- Run 1: the degree condition first (graphs with f ≤ 3: 6 768, 48 129, 304 993, 3 007 585 for
  n = 11..14), then an exact backtracking 3-colouring test on these: all are 3-colourable.
  Without the degree condition: 0 graphs for n ≤ 10 and 1, 24, 1110 for n = 11, 12, 13.
- Run 2: the 3-colouring test on every graph first, then f on the graphs kept (the two
  right-hand columns are from this run). Its colouring test was compared with brute force on all
  13 598 graphs with at most 8 vertices, and a second solver was run over the complete n = 13
  and n = 14 generations with identical output.

The runs agree on every number they have in common, including the counts of the four parts at
n = 14, and on the sets of non-3-colourable graphs for n = 11, 12, 13. Both use the same
generator, so an error in `geng` itself would not be detected.

Triangle-free graphs with f ≤ 2 (the program of run 1 with a 2-colouring test; a single run):

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| triangle-free graphs with f ≤ 2 | 1 | 2 | 2 | 3 | 2 | 3 | 4 | 7 | 5 | 9 | 13 | 23 | 17 | 46 |
| of these not bipartite | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

## 6. Code and data availability

`computations/efs_f4/` contains the programs of both runs, the logs and report of the
independent run, the graph6 lists of all triangle-free graphs that are not 3-colourable for
n = 11, 12, 13, 14 (1, 24, 1 110 and 76 261 graphs), and a README with the exact commands, tool
versions and expected counts. The Lean files are in `Proofs/`.

## 7. F(5) ≤ 34 — search only

**Not formalized, not shown to be optimal, one search.** F(5) ≥ 22 by [JR]. A local search over
triangle-free supergraphs of the Mycielskian of the Grötzsch graph (23 vertices, chromatic number
5) found graphs with f = 3 on 34, 36, 38 and 40 vertices, and none on 23–32 in the starts tried.
The 34-vertex graph: 116 edges, triangle-free, degrees 1, 2,2,2, 3,3,3, …, 12,12,12, vertices
0..22 carry the core (so it is not 4-colourable), 5-colourable. Edges
(also `computations/efs_f4/search/f5_n34_edges.txt`):

    (0,1), (0,4), (0,6), (0,9), (0,12), (0,15), (0,17), (0,20), (0,25), (0,26), (0,30), (1,2),
    (1,5), (1,7), (1,11), (1,13), (1,16), (1,18), (1,32), (1,33), (2,3), (2,6), (2,8), (2,12),
    (2,14), (2,17), (2,19), (2,27), (2,28), (2,29), (3,4), (3,7), (3,9), (3,13), (3,15), (3,18),
    (3,20), (3,23), (3,25), (3,32), (3,33), (4,5), (4,8), (4,11), (4,14), (4,16), (4,19), (4,27),
    (5,10), (5,12), (5,15), (5,21), (5,29), (6,10), (6,11), (6,13), (6,21), (7,10), (7,12), (7,14),
    (7,21), (7,27), (7,28), (7,29), (8,10), (8,13), (8,15), (8,21), (9,10), (9,11), (9,14), (9,21),
    (9,24), (9,27), (9,28), (9,29), (9,31), (10,16), (10,17), (10,18), (10,19), (10,20), (10,32),
    (10,33), (11,22), (12,22), (12,32), (12,33), (13,22), (13,27), (13,29), (14,22), (14,23),
    (14,25), (14,30), (14,32), (14,33), (15,22), (15,27), (16,22), (16,29), (17,22), (18,22),
    (19,22), (20,22), (20,27), (21,22), (21,32), (21,33), (22,31), (26,27), (27,32), (27,33),
    (29,30), (29,32), (29,33)

## Declaration of generative AI use

In preparing this work the author used Claude (Anthropic) for the graph searches, the exhaustive
computations, the Lean formalization, the literature search and the drafting of this text. The
second run of the lower-bound computation was carried out by a separate Claude agent that was
given only the claim and wrote its own programs. The statements marked as checked by the Lean
kernel do not depend on these tools being right; the statements marked as computation do. The author directed the work, had its claims cross-checked by independent agents, and takes responsibility for it.

## References

- [EFS] P. Erdős, S. Fajtlowicz, W. Staton, Degree sequences in triangle-free graphs, Discrete
  Math. 92 (1991) 85–88.
- [BDF] T. L. Brewster, M. J. Dinneen, V. Faber, A computational attack on the conjectures of
  Graffiti: new counterexamples and proofs, Discrete Math. 147 (1995) 35–55.
- [JR] T. Jensen, G. F. Royle, Small graphs with chromatic number 5: a computer search, J. Graph
  Theory 19 (1995) 107–116. (Cited through [G]; not read.)
- [G] J. Goedgebeur, On minimal triangle-free 6-chromatic graphs, arXiv:1707.07581.
