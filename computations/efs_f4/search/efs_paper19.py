#!/usr/bin/env python3
"""efs_paper19: the 19-vertex graph of Erdos-Fajtlowicz-Staton (1991), built from the description
of its construction, and its properties.
Groetzsch graph: 5-cycle u0..u4 (vertices 0..4, degree 4), w_i (5+i, degree 3) adjacent to
u_{i-1}, u_{i+1}, apex z (10, degree 5) adjacent to all w_i.
 11       : adjacent to two non-adjacent degree-4 vertices (u0, u2)
 12,13,14 : each adjacent to the five degree-3 vertices w_0..w_4
 15,16,17 : each adjacent to 12, 13, 14
 18       : adjacent to two non-adjacent degree-6 vertices (w_0, w_1; the w_i have degree 6 now)"""
import collections, itertools, networkx as nx
E = [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, (i - 1) % 5) for i in range(5)] + \
    [(5 + i, (i + 1) % 5) for i in range(5)] + [(10, 5 + i) for i in range(5)]
G = nx.Graph(E); assert sorted(d for _, d in G.degree()) == [3] * 5 + [4] * 5 + [5]
assert not G.has_edge(0, 2)
G.add_edges_from([(11, 0), (11, 2)])
G.add_edges_from((b, 5 + i) for b in (12, 13, 14) for i in range(5))
G.add_edges_from((c, b) for c in (15, 16, 17) for b in (12, 13, 14))
assert G.degree(5) == 6 and G.degree(6) == 6 and not G.has_edge(5, 6)
G.add_edges_from([(18, 5), (18, 6)])
deg = sorted(d for _, d in G.degree()); cnt = collections.Counter(deg)
print("vertices", G.number_of_nodes(), "edges", G.number_of_edges())
print("triangles", sum(nx.triangles(G).values()) // 3)
print("degree sequence", " ".join(f"{d}^{cnt[d]}" for d in sorted(cnt)), "| f =", max(cnt.values()))
print("isolated vertices", sum(1 for d in deg if d == 0), "| connected", nx.is_connected(G))
def colourable(k):
    order = sorted(G, key=lambda v: -G.degree(v)); col = {}
    def go(i):
        if i == len(order): return True
        v = order[i]; used = {col[u] for u in G[v] if u in col}; mx = max(col.values(), default=-1) + 1
        for c in range(min(k, mx + 1)):
            if c not in used:
                col[v] = c
                if go(i + 1): return True
                del col[v]
        return False
    return go(0)
print("3-colourable", colourable(3), "| 4-colourable", colourable(4))
