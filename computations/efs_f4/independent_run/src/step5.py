#!/usr/bin/env python3
import itertools
from collections import Counter
E = [(0,1),(0,4),(0,6),(0,9),(0,11),(1,2),(1,5),(1,7),(1,12),(1,14),(2,3),(2,6),(2,8),(3,4),(3,7),(3,9),(3,11),(3,14),(4,5),(4,8),(4,12),(5,10),(5,11),(6,10),(7,10),(8,10),(8,11),(9,10),(10,13),(11,13)]
n = 15
assert len(set(map(frozenset, E))) == len(E) and all(a != b for a, b in E)
adj = [set() for _ in range(n)]
for a, b in E: adj[a].add(b); adj[b].add(a)
tris = [t for t in itertools.combinations(range(n), 3) if t[1] in adj[t[0]] and t[2] in adj[t[0]] and t[2] in adj[t[1]]]
deg = [len(a) for a in adj]
print("vertices", n, "edges", len(E))
print("triangles:", tris, "-> triangle-free:", not tris)
print("degrees by vertex:", deg)
print("degree sequence (sorted):", sorted(deg, reverse=True))
c = Counter(deg); print("degree multiplicities:", dict(sorted(c.items())), "f =", max(c.values()))
def colourable(k):
    # plain brute force: all k^(n-1) maps with vertex 0 fixed to colour 0
    for rest in itertools.product(range(k), repeat=n-1):
        col = (0,) + rest
        if all(col[a] != col[b] for a, b in E): return col
    return None
for k in (1, 2, 3, 4):
    w = colourable(k)
    print("k=%d colourable: %s%s" % (k, bool(w), ("  witness " + str(w)) if w else ""))
    if w: print("chromatic number =", k); break
# graph6 for cross-check with col3
bits = [1 if i in adj[j] else 0 for j in range(1, n) for i in range(j)]
bits += [0] * (-len(bits) % 6)
print("graph6:", chr(n + 63) + "".join(chr(63 + int("".join(map(str, bits[i:i+6])), 2)) for i in range(0, len(bits), 6)))
