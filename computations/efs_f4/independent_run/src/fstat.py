#!/usr/bin/env python3
"""Step 3: for graph6 lines on stdin, compute f(G) = max multiplicity of a degree; print distribution.
Also re-checks triangle-freeness of every kept graph."""
import sys
from collections import Counter
def dec(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> k) & 1 for k in (5, 4, 3, 2, 1, 0)]
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j); adj[j].add(i)
            k += 1
    return n, adj
dist = Counter(); tri = 0; tot = 0; minex = {}
for line in sys.stdin:
    s = line.strip()
    if not s: continue
    n, adj = dec(s)
    tot += 1
    if any(adj[u] & adj[v] for u in range(n) for v in adj[u]): tri += 1
    f = max(Counter(len(a) for a in adj).values())
    dist[f] += 1
    minex.setdefault(f, s)
print("graphs=%d with_triangle=%d" % (tot, tri))
if tot:
    print("f distribution: " + ", ".join("f=%d: %d" % (k, dist[k]) for k in sorted(dist)))
    m = min(dist); print("min f = %d (example %s)" % (m, minex[m]))
else:
    print("f distribution: (no graphs)")
