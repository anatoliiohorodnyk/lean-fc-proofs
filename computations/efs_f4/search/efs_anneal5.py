#!/usr/bin/env python3
"""efs_anneal5: upper bound for F(5).  Core: the Mycielskian of the Groetzsch graph (23 vertices,
triangle-free, chromatic number 5).  Look for a triangle-free supergraph on n >= 23 vertices in
which no degree occurs more than 3 times.  usage: efs_anneal5.py n [seeds] [iters]"""
import sys, random, math, networkx as nx
n = int(sys.argv[1]); seeds = int(sys.argv[2]) if len(sys.argv) > 2 else 10
iters = int(sys.argv[3]) if len(sys.argv) > 3 else 400000
M = nx.mycielskian(nx.mycielskian(nx.cycle_graph(5)))
assert M.number_of_nodes() == 23 and sum(nx.triangles(M).values()) == 0
core = {(min(a, b), max(a, b)) for a, b in M.edges()}
def colourable(adj, k, nn):
    order = sorted(range(nn), key=lambda v: -len(adj[v])); col = {}
    def go(i):
        if i == nn: return True
        v = order[i]; used = {col[u] for u in adj[v] if u in col}
        mx = max(col.values(), default=-1) + 1
        for c in range(min(k, mx + 1)):
            if c not in used:
                col[v] = c
                if go(i + 1): return True
                del col[v]
        return False
    return go(0)
adj0 = [set() for _ in range(23)]
for a, b in core: adj0[a].add(b); adj0[b].add(a)
assert not colourable(adj0, 4, 23) and colourable(adj0, 5, 23)
def cost(adj):
    cnt = {}
    for v in range(n): cnt[len(adj[v])] = cnt.get(len(adj[v]), 0) + 1
    return sum(max(0, c - 3) for c in cnt.values())
bestc = 99
for seed in range(seeds):
    rnd = random.Random(1000 * n + seed)
    adj = [set() for _ in range(n)]
    for a, b in core: adj[a].add(b); adj[b].add(a)
    c = cost(adj); T = 1.0
    for it in range(iters):
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
        T = max(0.05, T * 0.99998)
        if c == 0: break
    bestc = min(bestc, c)
    if c == 0:
        E = sorted((a, b) for a in range(n) for b in adj[a] if a < b)
        assert not any(adj[a] & adj[b] for a, b in E)
        five = colourable(adj, 5, n)
        degs = sorted(len(adj[v]) for v in range(n))
        print("FOUND n=%d seed=%d edges=%d 5-colourable=%s degrees=%s" % (n, seed, len(E), five, degs)); print(E)
        sys.exit(0)
print("n=%d: nothing found in %d seeds (best excess %d)" % (n, seeds, bestc))
