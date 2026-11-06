# Lean의 IsPlanar 정의를 그대로 옮겨, 작은 그래프에서 알려진 평면성과 비교한다.
import itertools, sys

def cyclic_orders(nbrs):
    if len(nbrs) <= 1:
        yield {w: w for w in nbrs}; return
    first, rest = nbrs[0], nbrs[1:]
    for p in itertools.permutations(rest):
        cyc = (first,) + p
        yield {cyc[i]: cyc[(i + 1) % len(cyc)] for i in range(len(cyc))}

def components(n, adj):
    seen, c = set(), 0
    for s in range(n):
        if s in seen: continue
        c += 1; st = [s]; seen.add(s)
        while st:
            u = st.pop()
            for w in adj[u]:
                if w not in seen: seen.add(w); st.append(w)
    return c

def is_planar_def(n, edges):
    adj = {v: sorted({w for e in edges for w in e if v in e and w != v}) for v in range(n)}
    E = len(edges); c = components(n, adj)
    iso = sum(1 for v in range(n) if not adj[v])
    darts = [(u, w) for u in range(n) for w in adj[u]]
    for rots in itertools.product(*[list(cyclic_orders(adj[v])) for v in range(n)]):
        rot = lambda d: (d[0], rots[d[0]][d[1]])
        phi = lambda d: rot((d[1], d[0]))
        seen, F = set(), 0
        for d in darts:
            if d in seen: continue
            F += 1; x = d
            while x not in seen: seen.add(x); x = phi(x)
        if n - E + F + iso == 2 * c:
            return True
    return False

def complete(n): return [(i, j) for i in range(n) for j in range(i + 1, n)]
named = {
  "empty(0)": (0, []), "K1": (1, []), "K2": (2, [(0,1)]), "2K1": (2, []),
  "K4": (4, complete(4)), "K5": (5, complete(5)), "K5-e": (5, complete(5)[1:]),
  "K3,3": (6, [(i, j) for i in range(3) for j in range(3, 6)]),
  "K3,3-e": (6, [(i, j) for i in range(3) for j in range(3, 6)][1:]),
  "star K1,3": (4, [(0,1),(0,2),(0,3)]), "2 triangles": (6, [(0,1),(1,2),(0,2),(3,4),(4,5),(3,5)]),
  "K4+K1": (5, complete(4)), "K5+K1": (6, complete(5)), "K5 ⊔ K4": (9, complete(5) + [(a+5,b+5) for a,b in complete(4)]),
  "octahedron": (6, [e for e in complete(6) if e not in [(0,1),(2,3),(4,5)]]),
  "cube Q3": (8, [(a, b) for a in range(8) for b in range(a+1, 8) if bin(a ^ b).count("1") == 1]),
  "Petersen": (10, [(i,(i+1)%5) for i in range(5)] + [(i,i+5) for i in range(5)] + [(5+i,5+(i+2)%5) for i in range(5)]),
  "K3,3 subdivided": (7, [(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,6),(6,5)]),
}
expected = {"K5": False, "K3,3": False, "K5+K1": False, "K5 ⊔ K4": False, "Petersen": False, "K3,3 subdivided": False}
ok = True
for name, (n, es) in named.items():
    es = [tuple(sorted(e)) for e in es]
    got = is_planar_def(n, es); exp = expected.get(name, True)
    ok &= got == exp
    print(f"{name:18s} 정의={got!s:5s} 기대={exp!s:5s} {'OK' if got == exp else '불일치!'}")
# 꼭짓점 5개 이하 모든 그래프: K5만 비평면이어야 한다.
for n in range(1, 6):
    allE = complete(n); bad = []
    for mask in range(1 << len(allE)):
        es = [allE[i] for i in range(len(allE)) if mask >> i & 1]
        if not is_planar_def(n, es): bad.append(len(es))
    exp = [10] if n == 5 else []
    ok &= bad == exp
    print(f"n={n}: 2^{len(allE)}개 그래프 중 비평면 {len(bad)}개 (변 수 {bad}) {'OK' if bad == exp else '불일치!'}")
print("ALL OK" if ok else "MISMATCH"); sys.exit(0 if ok else 1)
