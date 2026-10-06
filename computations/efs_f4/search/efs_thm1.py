#!/usr/bin/env python3
"""efs_thm1: test `theorem1` and `lemma3` of DegreeSequencesTriangleFree.lean as formalized.
theorem1: connected, triangle-free, degreeSequenceMultiplicity = 2  =>  bipartite, min degree 1,
          sorted degree sequence d satisfies d[k+2] = d[k] + 1 for all k with k + 2 < n.
lemma3 (n = 1): a bipartite graph on 8 vertices with min degree 2 and multiplicity 3 exists."""
import sys, subprocess, collections, networkx as nx
def mult(G): return max(collections.Counter(d for _, d in G.degree()).values())
for n in range(2, 12):
    out = subprocess.run(["nauty-geng", "-q", "-c", "-t", str(n)], capture_output=True).stdout.split()
    hyp = bad = 0; ex = []
    for g6 in out:
        G = nx.from_graph6_bytes(g6)
        if mult(G) != 2: continue
        hyp += 1
        d = sorted(x for _, x in G.degree())
        ok = nx.is_bipartite(G) and d[0] == 1 and all(d[k + 2] == d[k] + 1 for k in range(n - 2))
        if not ok: bad += 1
        if len(ex) < 2: ex.append((g6.decode(), d))
    print(f"theorem1 n={n}: connected triangle-free graphs {len(out)}, with f=2: {hyp}, violations {bad}", ex[:1])
out = subprocess.run(["nauty-geng", "-q", "-b", "-d2", "8"], capture_output=True).stdout.split()
hits = [g for g in out if mult(nx.from_graph6_bytes(g)) == 3]
print("lemma3 n=1: bipartite graphs on 8 vertices with min degree >= 2:", len(out), "with f = 3 and min degree exactly 2:",
      sum(1 for g in hits if min(d for _, d in nx.from_graph6_bytes(g).degree()) == 2))
