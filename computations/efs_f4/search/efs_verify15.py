#!/usr/bin/env python3
"""efs_verify15: independent check (networkx + brute force over all 3^15 colourings is avoided:
exact chromatic number by exhaustive search with symmetry only on the first vertex) of the
15-vertex graph found by efs_anneal.py."""
import itertools, collections, networkx as nx
E = [(0, 1), (0, 4), (0, 6), (0, 9), (0, 11), (1, 2), (1, 5), (1, 7), (1, 12), (1, 14), (2, 3), (2, 6), (2, 8), (3, 4), (3, 7), (3, 9), (3, 11), (3, 14), (4, 5), (4, 8), (4, 12), (5, 10), (5, 11), (6, 10), (7, 10), (8, 10), (8, 11), (9, 10), (10, 13), (11, 13)]
G = nx.Graph(E); n = G.number_of_nodes()
print("vertices", n, "edges", G.number_of_edges(), "connected", nx.is_connected(G))
print("triangles", sum(nx.triangles(G).values()) // 3)
deg = sorted(d for _, d in G.degree()); print("degrees", deg, "max multiplicity", max(collections.Counter(deg).values()))
def colourable(k):
    order = list(range(n)); col = {}
    def go(i):
        if i == n: return True
        v = order[i]
        for c in range(k):
            if all(col.get(u) != c for u in G[v]):
                col[v] = c
                if go(i + 1): return True
                del col[v]
        return False
    return go(0)
print("3-colourable", colourable(3), "4-colourable", colourable(4))
H = G.subgraph(range(11)); M = nx.mycielskian(nx.cycle_graph(5))
print("vertices 0..10 contain the Groetzsch graph as a spanning subgraph of the induced graph:",
      nx.algorithms.isomorphism.GraphMatcher(H, M).subgraph_is_monomorphic(), "| induced edges", H.number_of_edges())
print("graph6:", nx.to_graph6_bytes(G, header=False).decode().strip())
