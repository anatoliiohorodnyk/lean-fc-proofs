#!/usr/bin/env python3
"""efs_anneal: look for a triangle-free graph on n vertices that contains the Groetzsch graph
(hence chromatic number >= 4) and in which no degree occurs more than 3 times.
Random local search over the non-core edges.  usage: efs_anneal.py n [seeds]"""
import sys, random, math
n = int(sys.argv[1]); seeds = int(sys.argv[2]) if len(sys.argv) > 2 else 20
core = [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, (i - 1) % 5) for i in range(5)] + \
       [(5 + i, (i + 1) % 5) for i in range(5)] + [(10, 5 + i) for i in range(5)]
core = {(min(a, b), max(a, b)) for a, b in core}
def cost(adj):
    cnt = {}
    for v in range(n): cnt[len(adj[v])] = cnt.get(len(adj[v]), 0) + 1
    return sum(max(0, c - 3) for c in cnt.values())
def colourable(adj, k):
    col = [-1] * n
    def go(v):
        if v == n: return True
        used = {col[u] for u in adj[v] if u < v}
        mx = max(col[:v], default=-1) + 1
        for c in range(min(k, mx + 1)):
            if c not in used:
                col[v] = c
                if go(v + 1): return True
        return False
    return go(0)
best = None
for seed in range(seeds):
    rnd = random.Random(seed)
    adj = [set() for _ in range(n)]
    for a, b in core: adj[a].add(b); adj[b].add(a)
    c = cost(adj); T = 1.0
    for it in range(200000):
        a, b = rnd.sample(range(n), 2); a, b = min(a, b), max(a, b)
        if (a, b) in core: continue
        if b in adj[a]:
            adj[a].discard(b); adj[b].discard(a); c2 = cost(adj)
            if c2 <= c or rnd.random() < math.exp((c - c2) / T): c = c2
            else: adj[a].add(b); adj[b].add(a)
        else:
            if adj[a] & adj[b]: continue
            adj[a].add(b); adj[b].add(a); c2 = cost(adj)
            if c2 <= c or rnd.random() < math.exp((c - c2) / T): c = c2
            else: adj[a].discard(b); adj[b].discard(a)
        T = max(0.05, T * 0.99995)
        if c == 0: break
    if c == 0:
        E = sorted((a, b) for a in range(n) for b in adj[a] if a < b)
        assert not any(adj[a] & adj[b] for a, b in E)
        assert not colourable(adj, 3) and colourable(adj, 4)
        degs = sorted(len(adj[v]) for v in range(n))
        print("FOUND n=%d seed=%d edges=%d degrees=%s" % (n, seed, len(E), degs)); print(E)
        best = E; break
if best is None: print("n=%d: nothing found in %d seeds" % (n, seeds))
