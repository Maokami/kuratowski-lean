# 블루프린트(blueprint/src)의 새 보조정리 진술을 작은 그래프에서 전수 검사한다.
# 각 검사 이름([J1] 등)은 블루프린트의 \bfcheck{...} 표시와 같다.
# 회전 체계·면·평면성 정의는 Kuratowski/Basic.lean과 같다 (scripts/check_definition.py와 같은 규약).
import itertools, sys

def adjacency(n, edges):
    adj = {v: set() for v in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    return {v: sorted(adj[v]) for v in range(n)}

def cyclic_orders(nbrs):
    if len(nbrs) <= 1:
        yield {w: w for w in nbrs}; return
    first, rest = nbrs[0], nbrs[1:]
    for p in itertools.permutations(rest):
        cyc = (first,) + p
        yield {cyc[i]: cyc[(i + 1) % len(cyc)] for i in range(len(cyc))}

def rotations(adj, verts, cap=None):
    lists = [list(cyclic_orders(adj[v])) for v in verts]
    total = 1
    for l in lists: total *= len(l)
    if cap and total > cap: return None
    return (dict(zip(verts, r)) for r in itertools.product(*lists))

def faces(adj, rot):
    darts = [(u, w) for u in adj for w in adj[u]]
    phi = lambda d: (d[1], rot[d[1]][d[0]])
    seen, orbs = set(), []
    for d in darts:
        if d in seen: continue
        o, x = [], d
        while x not in seen: seen.add(x); o.append(x); x = phi(x)
        orbs.append(o)
    return orbs

def components(adj, verts):
    seen, c = set(), 0
    for s in verts:
        if s in seen: continue
        c += 1; st = [s]; seen.add(s)
        while st:
            u = st.pop()
            for w in adj[u]:
                if w not in seen: seen.add(w); st.append(w)
    return c

def euler_ok(adj, verts, rot):
    E = sum(len(adj[v]) for v in verts) // 2
    iso = sum(1 for v in verts if not adj[v])
    return len(verts) - E + len(faces(adj, rot)) + iso == 2 * components(adj, verts)

def induced(adj, keep):
    return {v: [w for w in adj[v] if w in keep] for v in keep}

def connected(adj, verts):
    return len(verts) > 0 and components(adj, verts) == 1

def support(adj):
    """지지 집합: 고립점이 아닌 꼭짓점."""
    return [v for v in adj if adj[v]]

def remove_vertices(adj, S):
    """G - S: S에 닿는 변을 모두 지운다. 꼭짓점 집합은 그대로다 (고정된 V)."""
    S = set(S)
    return {v: ([] if v in S else [w for w in adj[v] if w not in S]) for v in adj}

def connected_within(adj, A):
    """A의 점들이 그래프 adj에서 서로 이어져 있는가 (A가 비면 참)."""
    A = set(A)
    if not A: return True
    s = next(iter(A)); seen = {s}; st = [s]
    while st:
        u = st.pop()
        for w in adj[u]:
            if w not in seen: seen.add(w); st.append(w)
    return A <= seen

def k_connected_on(adj, base, k):
    """점 집합 base가 G에서 k-연결: |base| > k이고, 꼭짓점 S를 k-1개 이하로 지워도 base - S가
    G - S에서 서로 이어져 있다. 지운 뒤 지지 집합을 다시 계산하지 않는다 (정의 def:conn3)."""
    base = set(base)
    if len(base) <= k: return False
    for r in range(k):
        for S in itertools.combinations(list(adj), r):
            if not connected_within(remove_vertices(adj, S), base - set(S)): return False
    return True

def k_connected(adj, k):
    """정의 def:conn3: 지지 집합 기준 k-연결."""
    return k_connected_on(adj, support(adj), k)

def planar(adj, cap=2_000_000):
    verts = list(adj)
    rs = rotations(adj, verts, cap)
    if rs is None: return None
    return any(euler_ok(adj, verts, r) for r in rs)

ok = True
def report(name, good, detail=""):
    global ok
    ok &= good
    print(f"{'OK ' if good else '실패'} {name} {detail}")

# ---------------------------------------------------------------------------
# [cyclic] 사이클 위 순환 단어 보조정리 (Diestel 4.4절 증명의 경우 나누기).
# 사이클 C의 각 자리는 x의 이웃(X), y의 이웃(Y), 둘 다(B), 둘 다 아님(-)이다.
# x의 이웃(X∪B)과 y의 이웃(Y∪B)이 각각 2개 이상이면 다음 중 하나가 성립한다.
#  (a) y의 이웃이 모두 연속한 두 x-이웃 사이의 닫힌 구간에 있다 (나눠서 매장 가능)
#  (b) 공통 이웃 B가 3개 이상 (TK5)
#  (c) y의 이웃 u, w가 있어 C - {u, w}의 두 호에 모두 x-이웃이 있다 (TK3,3)
def cyclic_case(word):
    n = len(word)
    xs = [i for i in range(n) if word[i] in "XB"]
    ys = [i for i in range(n) if word[i] in "YB"]
    def arc(i, j):  # i에서 j까지 (양 끝 포함) 시계 방향
        k, out = i, [i]
        while k != j: k = (k + 1) % n; out.append(k)
        return out
    a = any(set(ys) <= set(arc(xs[t], xs[(t + 1) % len(xs)])) for t in range(len(xs)))
    b = sum(1 for c in word if c == "B") >= 3
    c = False
    for u, w in itertools.combinations(ys, 2):
        inner1, inner2 = arc(u, w)[1:-1], arc(w, u)[1:-1]
        if any(word[i] in "XB" for i in inner1) and any(word[i] in "XB" for i in inner2):
            c = True; break
    return a, b, c

cnt = 0; bad = []
for n in range(2, 10):
    for word in itertools.product("XYB-", repeat=n):
        if sum(c in "XB" for c in word) < 2 or sum(c in "YB" for c in word) < 2: continue
        cnt += 1
        a, b, c = cyclic_case(word)
        if not (a or b or c): bad.append("".join(word))
report("[cyclic] 순환 단어 경우 나누기", not bad, f"({cnt}개 단어, 반례 {bad[:3]})")

# ---------------------------------------------------------------------------
# 작은 그래프 모음: 꼭짓점 5개 이하 전부 + 이름 있는 평면 그래프 몇 개.
def complete(n): return [(i, j) for i in range(n) for j in range(i + 1, n)]
graphs = []
for n in range(3, 6):
    allE = complete(n)
    for mask in range(1 << len(allE)):
        graphs.append((n, [allE[i] for i in range(len(allE)) if mask >> i & 1]))
wheel = lambda k: (k + 1, [(i, (i + 1) % k) for i in range(k)] + [(i, k) for i in range(k)])
named = {
    "W5": wheel(5), "W6": wheel(6),
    "prism": (6, [(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)]),
    "octahedron": (6, [e for e in complete(6) if e not in [(0,1),(2,3),(4,5)]]),
    "cube": (8, [(a, b) for a in range(8) for b in range(a+1, 8) if bin(a ^ b).count("1") == 1]),
    "K3,3-e": (6, [(i, j) for i in range(3) for j in range(3, 6)][1:]),
}
graphs += list(named.values())

# ---------------------------------------------------------------------------
# [split2] 같은 면의 두 모서리에서 꼭짓점 쪼개기 (블루프린트 lem:split2).
# 회전 r[u][x]는 u 둘레에서 x 다음 이웃이다. 다트 (u, x)에 대해 ρ(u, x) = (u, r[u][x])이고
# 면 순열은 φ(u, x) = ρ(x, u)다 (faces와 같은 규약).
# 같은 꼭짓점 w로 들어오는 서로 다른 두 다트 e1, e2를 고르고 ρ' = ρ ∘ (ē1 ē2)로 둔다.
# w의 다트는 ρ'에서 두 순환으로 나뉜다. ē2의 순환 B를 새 꼭짓점 n(Lean의 none)에 붙인다.
# 다트 d는 (B에 있으면 n, 아니면 d의 시작점) → (d̄가 B에 있으면 n, 아니면 d의 끝점)으로 옮긴다.
#  양성: e1, e2가 같은 면이면 n' = n + 1, E' = E, I' = I, O' = O + 1, 곧 χ' = χ + 2.
#        성분은 어떤 a ∈ A, b ∈ B의 끝점이 G - w에서 이어지면 c' = c, 그런 쌍이 없으면 c' = c + 1.
#  음성: e1, e2가 다른 면이면 두 면이 합쳐져 O' = O - 1이다 (같은 면 가정이 필요하다).
#  경계: 경로 0-1-2에서 w = 1을 쪼개면 w가 절단점이라 c' = c + 1이다.
# 규모: 꼭짓점 5개 이하의 모든 그래프와 모든 회전 체계 (이름 있는 큰 그래프는 넣지 않는다).
# ---------------------------------------------------------------------------
def split2_apply(n, adj, r, e1, e2):
    rho = {(u, x): (u, r[u][x]) for u in adj for x in adj[u]}
    rev = lambda d: (d[1], d[0])
    a1, a2 = rev(e1), rev(e2)
    sw = {a1: a2, a2: a1}
    rho2 = {d: rho[sw.get(d, d)] for d in rho}
    B, cur = set(), a2
    while cur not in B:
        B.add(cur); cur = rho2[cur]
    pairs = {d: (n if d in B else d[0], n if rev(d) in B else d[1]) for d in rho}
    if any(a == b for a, b in pairs.values()): return None
    if len(set(pairs.values())) != len(pairs): return None
    adj2 = adjacency(n + 1, sorted({tuple(sorted(p)) for p in pairs.values()}))
    r2 = {a: {} for a in range(n + 1)}
    for d, (a, b) in pairs.items():
        a_next, b_next = pairs[rho2[d]]
        if a_next != a: return None
        r2[a][b] = b_next
    for a in adj2:
        if set(r2[a]) != set(adj2[a]) or set(r2[a].values()) != set(adj2[a]): return None
        if adj2[a]:
            start, cur, seen = adj2[a][0], r2[a][adj2[a][0]], 1
            while cur != start: cur = r2[a][cur]; seen += 1
            if seen != len(adj2[a]): return None
    return adj2, r2, B

def split2_counts(adj, r):
    E = sum(len(adj[v]) for v in adj) // 2
    O = len(faces(adj, r))
    I = sum(1 for v in adj if not adj[v])
    return len(adj), E, O, I, components(adj, list(adj))

def split2_linked(adj, w, A, B):
    """어떤 A의 점과 어떤 B의 점이 G - w에서 이어지는가 (A 전체에서 시작하는 탐색)."""
    rest = remove_vertices(adj, {w})
    seen, st = set(A), list(A)
    while st:
        u = st.pop()
        for x in rest[u]:
            if x not in seen: seen.add(x); st.append(x)
    return bool(seen & set(B))

split2_pos = split2_cut = split2_neg = split2_neg_merge = 0
split2_bad = []
for n, es in graphs:
    if n > 5: continue
    adj = adjacency(n, es)
    for r in rotations(adj, list(adj)):
        fs = faces(adj, r)
        face_of = {d: i for i, f in enumerate(fs) for d in f}
        n0, E0, O0, I0, C0 = split2_counts(adj, r)
        incoming = {}
        for d in face_of: incoming.setdefault(d[1], []).append(d)
        for w, ins in incoming.items():
            for e1, e2 in itertools.combinations(ins, 2):
                res = split2_apply(n, adj, r, e1, e2)
                if res is None:
                    split2_bad.append(("구성", n, es, e1, e2)); continue
                adj2, r2, B = res
                n1, E1, O1, I1, C1 = split2_counts(adj2, r2)
                if face_of[e1] == face_of[e2]:
                    split2_pos += 1
                    A_nb = [x for x in adj[w] if (w, x) not in B]
                    B_nb = [x for x in adj[w] if (w, x) in B]
                    linked = split2_linked(adj, w, A_nb, B_nb)
                    good = (n1 == n0 + 1 and E1 == E0 and I1 == I0 and O1 == O0 + 1
                            and (n1 - E1 + O1 + I1) == (n0 - E0 + O0 + I0) + 2
                            and C1 == C0 + (0 if linked else 1))
                    if not good: split2_bad.append(("양성", n, es, e1, e2))
                    if n == 3 and sorted(es) == [(0, 1), (1, 2)] and w == 1:
                        split2_cut += (not linked) and C1 == C0 + 1
                else:
                    split2_neg += 1
                    split2_neg_merge += O1 == O0 - 1
report("[split2] 같은 면의 두 모서리에서 쪼개면 χ가 2 늘고 성분 조건이 맞는다", not split2_bad,
       f"({split2_pos}개 경우, 반례 {split2_bad[:1]})")
report("[split2-음성] 다른 면의 두 다트로 쪼개면 면이 합쳐진다 (O' = O - 1)",
       split2_neg > 0 and split2_neg_merge == split2_neg, f"({split2_neg}개 경우)")
report("[split2-절단점] 경로 0-1-2의 가운데를 쪼개면 c' = c + 1", split2_cut > 0,
       f"({split2_cut}개 경우)")

# [sum2-수술] 공통 변 01을 따라 붙인다. 평행 변을 가진 중간 상태는 그래프가 아니라
# 태그가 붙은 두 다트 집합의 순열이다. 원래 회전이 종수 0이 아닌 경우도 면 순환 식을 검사한다.
# rho0 = rho * swap(p, rho2^-1(q)) * swap(rho1^-1(p.symm), q.symm).
# 두각형 {p.symm, q}를 만든 뒤 q와 q.symm을 잘라 내고 G1 쪽 공통 변을 남긴다.
def sum2_perm_orbits(perm):
    todo, result = set(perm), []
    while todo:
        cur = next(iter(todo)); orb = []
        while cur in todo:
            todo.remove(cur); orb.append(cur); cur = perm[cur]
        if cur != orb[0]:
            raise ValueError("순열의 서로 다른 순환이 겹침")
        result.append(orb)
    return result

def sum2_cut_perm(perm, point):
    perm = perm.copy()
    predecessor = next(d for d in perm if perm[d] == point)
    perm[predecessor], perm[point] = perm[point], point
    return perm

def sum2_surgery_ok(n, edges1, edges2, r1, r2, variant=None):
    adj1, adj2 = adjacency(n, edges1), adjacency(n, edges2)
    rho = {(side,u,v): (side,u,r[u][v]) for side, adj, r in [(0,adj1,r1),(1,adj2,r2)]
        for u in adj for v in adj[u]}
    sym = lambda d: (d[0],d[2],d[1])
    pred = {v:k for k,v in rho.items()}
    p, q = (0,0,1), (1,0,1)
    a, b = pred[q], pred[sym(p)]
    if variant == 'x': a = q
    if variant == 'y': b = sym(p)
    rho[p], rho[a] = rho[a], rho[p]
    rho[b], rho[sym(q)] = rho[sym(q)], rho[b]
    phi = {d:rho[sym(d)] for d in rho}
    bigon = phi[sym(p)] == q and phi[q] == sym(p)
    source_orbits = len(faces(adj1,r1)) + len(faces(adj2,r2))
    before = len(sum2_perm_orbits(phi))
    rho = sum2_cut_perm(sum2_cut_perm(rho,q),sym(q))
    keep = set(rho) - {q,sym(q)}
    if not all(rho[d] in keep and rho[d][1] == d[1] for d in keep): return False
    result = {u:{} for u in range(n)}
    for d in keep:
        if d[2] in result[d[1]]: return False
        result[d[1]][d[2]] = rho[d][2]
    adj = adjacency(n,sorted(set(edges1)|set(edges2)))
    if not all(set(result[u]) == set(adj[u]) and set(result[u].values()) == set(adj[u])
               for u in adj): return False
    if not all(not result[u] or len(sum2_perm_orbits(result[u])) == 1 for u in adj): return False
    good = bigon and before == source_orbits and len(faces(adj,result))+1 == source_orbits
    if euler_ok(adj1,list(adj1),r1) and euler_ok(adj2,list(adj2),r2):
        good &= euler_ok(adj,list(adj),result)
    return good

# 배정에서 어느 쪽에 놓였어도 실제 변이 없는 점은 공통 고립점이다. 서로 다른 배정이
# 같은 (n, E1, E2)를 만들 수 있으므로 seen으로 중복을 뺀다. 작은 쌍은 n별 1, 7, 81, 1527개다.
sum2_seen, sum2_count, sum2_mutations = set(), 0, {'x':0,'y':0}
sum2_cache = {}
sum2_bad = []
def sum2_all_rot(n,edges):
    key = n,edges
    if key not in sum2_cache: sum2_cache[key] = list(rotations(adjacency(n,edges),list(range(n))))
    return sum2_cache[key]

def sum2_check_pair(n,e1,e2):
    global sum2_count
    key = n,e1,e2
    if key in sum2_seen: return
    sum2_seen.add(key)
    adj1, adj2 = adjacency(n,e1), adjacency(n,e2)
    adj = adjacency(n,sorted(set(e1)|set(e2)))
    counts_ok = (set(support(adj1)) & set(support(adj2)) == {0,1}
                 and len(set(e1)|set(e2))+1 == len(e1)+len(e2))
    iso = lambda a: sum(not a[v] for v in a)
    counts_ok &= iso(adj)+n == iso(adj1)+iso(adj2)+2
    counts_ok &= components(adj,list(adj))+n == components(adj1,list(adj1))+components(adj2,list(adj2))+1
    if not counts_ok:
        sum2_bad.append(("개수 식",n,e1,e2))
        return
    for r1 in sum2_all_rot(n,e1):
        for r2 in sum2_all_rot(n,e2):
            sum2_count += 1
            if not sum2_surgery_ok(n,e1,e2,r1,r2): sum2_bad.append(("회전 수술",n,e1,e2))
            for variant in sum2_mutations:
                sum2_mutations[variant] += not sum2_surgery_ok(n,e1,e2,r1,r2,variant)

for n in range(2,6):
    for assignment in itertools.product(range(3),repeat=n-2):
        sets = [{0,1}|{i+2 for i,a in enumerate(assignment) if a==side} for side in [0,1]]
        candidates = [[e for e in itertools.combinations(sorted(s),2) if e!=(0,1)] for s in sets]
        lists = [sorted(set(tuple(sorted([(0,1)]+[e for i,e in enumerate(es) if mask>>i&1]))
            for mask in range(1<<len(es)))) for es in candidates]
        for e1 in lists[0]:
            for e2 in lists[1]: sum2_check_pair(n,e1,e2)
# 공통 변을 따라 K4 둘을 붙이고 꼭짓점 6은 공통 고립점으로 둔다.
sum2_check_pair(7,tuple(itertools.combinations([0,1,2,3],2)),tuple(itertools.combinations([0,1,4,5],2)))

report("[sum2-수술] 공통 변의 두각형을 만들고 중복 변을 지운다", not sum2_bad,
       f"({len(sum2_seen)}개 그래프 쌍, {sum2_count}개 회전 쌍, 반례 {sum2_bad[:1]})")
report("[sum2-수술-음성] 선행 다트 선택을 바꾸면 두각형·면 수 조건에 반례", all(sum2_mutations.values()),
       f"(x 쪽 변이 {sum2_mutations['x']}개, y 쪽 변이 {sum2_mutations['y']}개)")
sum2_cache.clear()

# [J1] 2-연결 그래프의 종수 0 회전 체계에서 면 경계는 사이클이다 (꼭짓점이 반복되지 않는다).
cnt = 0; bad = []
for n, es in graphs:
    adj = adjacency(n, es)
    if not k_connected(adj, 2): continue
    rs = rotations(adj, list(adj), cap=100_000)
    if rs is None: continue
    for r in rs:
        if not euler_ok(adj, list(adj), r): continue
        cnt += 1
        for f in faces(adj, r):
            vs = [d[0] for d in f]
            if len(set(vs)) != len(vs): bad.append((n, es)); break
report("[J1] 2-연결 + 종수 0 → 면 경계가 사이클", not bad, f"({cnt}개 회전 체계)")

# [J1-음성] 종수 0 조건을 빼면 거짓이다: K4의 종수 0이 아닌 회전 체계에는 꼭짓점이 반복되는 면이 있다.
K4 = adjacency(4, complete(4))
nonzero = [r for r in rotations(K4, list(K4)) if not euler_ok(K4, list(K4), r)]
repeat = [r for r in nonzero
          if any(len({d[0] for d in f}) != len(f) for f in faces(K4, r))]
report("[J1-음성] 종수 0 조건을 빼면 K4에서 반례", len(repeat) > 0,
       f"(종수 0이 아닌 회전 체계 {len(nonzero)}개 중 반례 {len(repeat)}개)")

# [J2] 종수 0 회전 체계에서 v의 이웃이 2개 이상이고 H의 지지 집합에서 v를 뺀 집합이 H - v에서
#      2-연결이면 (k_connected_on), H - v의 (유도된 회전 체계의) 한 면이 v의 이웃을 모두 v 둘레
#      순서의 역순으로 지나는 사이클이다. H - v의 지지 집합을 다시 계산한 2-연결은 가정으로 부족하다
#      (아래 [J2-반례]).
def j2_hyp(adj, v):
    return len(adj[v]) >= 2 and k_connected_on(remove_vertices(adj, [v]), set(support(adj)) - {v}, 2)

def j2_concl(adj, r, v):
    keep = set(adj) - {v}
    sub = induced(adj, keep)
    rsub = {}
    for u in keep:  # 유도된 회전: v를 건너뛴다
        if not adj[u]: rsub[u] = {}; continue
        order, w = [], adj[u][0]
        for _ in range(len(adj[u])): order.append(w); w = r[u][w]
        order = [w for w in order if w != v]
        rsub[u] = {order[i]: order[(i + 1) % len(order)] for i in range(len(order))}
    nb, w = [], adj[v][0]
    for _ in range(len(adj[v])): nb.append(w); w = r[v][w]
    want = list(reversed(nb))
    for f in faces(sub, rsub):
        vs = [d[0] for d in f]
        if len(set(vs)) != len(vs) or not set(nb) <= set(vs): continue
        seq = [x for x in vs if x in nb]
        k = seq.index(want[0])
        if seq[k:] + seq[:k] == want: return True
    return False

cnt = 0; bad = []
for n, es in graphs:
    adj = adjacency(n, es)
    if n < 4: continue
    rs = rotations(adj, list(adj), cap=100_000)
    if rs is None: continue
    for r in rs:
        if not euler_ok(adj, list(adj), r): continue
        for v in adj:
            if not j2_hyp(adj, v): continue
            cnt += 1
            if not j2_concl(adj, r, v): bad.append((n, es, v))
report("[J2] 꼭짓점을 지우면 이웃을 순서대로 지나는 면 사이클", not bad, f"({cnt}개 경우)")

# [J2-반례] 가정을 "H - v의 지지 집합을 다시 계산해 2-연결"로 약하게 하면 거짓이다 (Codex 검토).
# H: 삼각형 012, 3을 0과 1에 잇고 잎 4를 3에 잇는다. v = 3. H - v는 삼각형 + 고립점 3, 4라서 지지 집합
# 기준으로는 2-연결이지만, v의 이웃 4는 H - v에서 고립점이라 이웃 {0, 1, 4}를 지나는 사이클이 없다.
H = adjacency(5, [(0, 1), (1, 2), (0, 2), (0, 3), (1, 3), (3, 4)])
weak = k_connected(remove_vertices(H, [3]), 2)
fails = [r for r in (rotations(H, list(H)) or []) if euler_ok(H, list(H), r) and not j2_concl(H, r, 3)]
report("[J2-반례] 약한 가정의 반례를 지금 가정이 배제한다",
       planar(H) is True and weak and not j2_hyp(H, 3) and len(fails) > 0,
       f"(H 평면 {planar(H)}, 약한 가정 {weak}, 지금 가정 {j2_hyp(H, 3)}, 결론이 틀린 회전 체계 {len(fails)}개)")

# [conn] 연결도 정의 (def:conn3): 지운 뒤 지지 집합을 다시 계산하지 않는다.
star = adjacency(4, [(0, 1), (0, 2), (0, 3)])
tri_iso = adjacency(4, [(0, 1), (1, 2), (0, 2)])
k4_iso = adjacency(5, complete(4))
path3 = adjacency(3, [(0, 1), (1, 2)])
conn_cases = [
    ("별 K1,3은 2-연결이 아니다 (중심을 지우면 잎들이 끊어진다)", k_connected(star, 2), False),
    ("별에서 중심을 지운 뒤 지지 집합을 다시 계산하면 비어서 공허하게 이어진다", support(remove_vertices(star, [0])) == [], True),
    ("삼각형 + 고립점은 2-연결이다 (지지 집합 기준)", k_connected(tri_iso, 2), True),
    ("K4 + 고립점은 3-연결이다", k_connected(k4_iso, 3), True),
    ("길이 2인 경로는 2-연결이 아니다", k_connected(path3, 2), False),
    ("[J2-반례]의 H는 2-연결이 아니다 (잎 4)", k_connected(H, 2), False),
]
bad = [name for name, got, want in conn_cases if got != want]
report("[conn] 지지 집합 기준 연결도의 작은 예", not bad, f"({len(conn_cases)}개 예, 틀림 {bad})")

# [S] 꼭짓점 나누기: G/xy의 종수 0 회전 체계에서 합친 꼭짓점 v 둘레의 이웃 순서가
#     "x쪽 구간 + y쪽 구간 (공통 이웃은 두 경계에만, 많아야 2개)"이면 G는 평면이다.
def contract(n, es, x, y):
    m = {i: i for i in range(n)}; m[y] = x
    ne = {tuple(sorted((m[a], m[b]))) for a, b in es if m[a] != m[b]}
    return adjacency(n, sorted(ne))

def interval_parse(word):
    # word: v 둘레 순서의 이웃 표시 (X: x만, Y: y만, B: 둘 다). 형태 B? X* B? Y* (순환)이면
    # (b1, X 위치들, b2, Y 위치들)을 돌려준다. b1, b2는 위치 또는 None.
    n = len(word)
    if n == 0: return None, [], None, []  # 빈 단어도 이 꼴이다
    for s in range(n):
        idx = [(s + i) % n for i in range(n)]
        i, b1, b2, xs, ys = 0, None, None, [], []
        if i < n and word[idx[i]] == "B": b1 = idx[i]; i += 1
        while i < n and word[idx[i]] == "X": xs.append(idx[i]); i += 1
        if i < n and word[idx[i]] == "B": b2 = idx[i]; i += 1
        while i < n and word[idx[i]] == "Y": ys.append(idx[i]); i += 1
        if i == n: return b1, xs, b2, ys
    return None

def interval_ok(word):
    return interval_parse(word) is not None

def cyc(rot_v, start):
    out, w = [], start
    for _ in range(len(rot_v)): out.append(w); w = rot_v[w]
    return out

def from_list(lst):
    return {lst[i]: lst[(i + 1) % len(lst)] for i in range(len(lst))}

cnt = 0; bad = []; skipped = 0
for n, es in graphs:
    adj = adjacency(n, es)
    for x, y in es:
        cadj = contract(n, es, x, y)
        verts = [u for u in cadj if u != y]
        cadj2 = {u: cadj[u] for u in verts}
        rs = rotations(cadj2, verts, cap=50_000)
        if rs is None: skipped += 1; continue
        hit = False
        for r in rs:
            if not euler_ok(cadj2, verts, r): continue
            nb = cyc(r[x], cadj2[x][0]) if cadj2[x] else []
            word = "".join("B" if (u in adj[x] and u in adj[y]) else ("X" if u in adj[x] else "Y")
                           for u in nb)
            if interval_ok(word): hit = True; break
        if hit:
            cnt += 1
            p = planar(adj)
            if p is False: bad.append((n, es, x, y))
            if p is None: skipped += 1
report("[S] 구간 조건을 만족하면 꼭짓점을 나눠도 평면", not bad, f"({cnt}개 경우, 건너뜀 {skipped})")
# [S-음성] 구간 조건이 실제로 무언가를 거른다: K5, K3,3은 비평면이지만 어느 변을 수축해도 평면이므로,
# 수축 그래프의 모든 종수 0 회전 체계에서 구간 조건이 실패해야 한다 ([S]의 대우).
K33 = (6, [(i, j) for i in range(3) for j in range(3, 6)])
neg_cnt = 0; neg_hit = []; nonplanar_ok = True
for name, (n, es) in {"K5": (5, complete(5)), "K3,3": K33}.items():
    adj = adjacency(n, es)
    nonplanar_ok &= planar(adj) is False
    for x, y in es + [(b, a) for a, b in es]:
        cadj = contract(n, es, x, y)
        verts = [u for u in cadj if u != y]
        cadj2 = {u: cadj[u] for u in verts}
        for r in rotations(cadj2, verts) or []:
            if not euler_ok(cadj2, verts, r): continue
            neg_cnt += 1
            nb = cyc(r[x], cadj2[x][0])
            word = "".join("B" if (u in adj[x] and u in adj[y]) else ("X" if u in adj[x] else "Y")
                           for u in nb)
            if interval_ok(word): neg_hit.append((name, x, y, word))
report("[S-음성] K5, K3,3의 수축에서는 구간 조건이 실패", nonplanar_ok and neg_cnt > 0 and not neg_hit,
       f"(종수 0 회전 체계 {neg_cnt}개, 구간 조건 성립 {len(neg_hit)}개)")

# 주의: [S]는 진술만 본다. 구간 조건이면 G에 종수 0 회전 체계가 "있는지"를 찾을 뿐, 증명의 수술이
# 만드는 회전 체계를 확인하지 않는다. 그것은 아래 [S-수술]이 한다.

# [S-수술] 보조정리 lem:S의 증명에 적은 수술. G/xy의 종수 0 회전 체계 R'에서 x 둘레 단어를
# b1 X... b2 Y... 로 읽으면 (b1, b2는 없을 수 있다) G의 회전 체계 R을 다음처럼 만든다.
#   x: (b1, X..., b2, y)    y: (b2, Y..., b1, x)
#   b1 둘레: R'에서 x 자리를 (x, y)로    b2 둘레: x 자리를 (y, x)로
#   Y 글자인 이웃 둘레: x 자리를 y로     그 밖의 꼭짓점: 그대로
# 이 R이 G의 회전 체계이고, 종수 0이며, 면 순열의 순환 수가 R'보다 |B|만큼 많은지 본다.
# 단, 단어가 비면(G/xy에서 x가 고립점) x, y 둘레는 서로뿐이고 xy 성분(K2)의 면 하나가 더해져 1만큼 많다.
def split_rotation(adj, r, x, y, nb, parse, variant=None):
    # variant: None = 증명의 수술, "b1swap" = b1 둘레를 (y, x)로, "yswap" = y 둘레에서 b1과 b2를 바꾼다
    b1, xs, b2, ys = parse
    B1 = nb[b1] if b1 is not None else None
    B2 = nb[b2] if b2 is not None else None
    X = [nb[i] for i in xs]; Y = [nb[i] for i in ys]
    opt = lambda b: [] if b is None else [b]
    R = {}
    for z in adj:
        if z == x: lst = opt(B1) + X + opt(B2) + [y]
        elif z == y:
            lst = (opt(B1) + Y + opt(B2) if variant == "yswap" else opt(B2) + Y + opt(B1)) + [x]
        elif not adj[z]: R[z] = {}; continue
        else:
            lst = []
            for w in cyc(r[z], next(iter(r[z]))):
                if w != x: lst.append(w)
                elif z == B1: lst += ([y, x] if variant == "b1swap" else [x, y])
                elif z == B2: lst += [y, x]
                elif z in Y: lst.append(y)
                else: lst.append(x)
        if sorted(lst) != sorted(adj[z]): return None  # 회전 체계가 아니다
        R[z] = from_list(lst)
    return R

def surgery_ok(adj, cadj2, r, x, y, nb, parse, word, variant=None):
    R = split_rotation(adj, r, x, y, nb, parse, variant)
    # 빈 단어이면 xy 성분(K2)의 면 하나가 더해진다.
    want = len(faces(cadj2, r)) + word.count("B") + (0 if word else 1)
    return R is not None and euler_ok(adj, list(adj), R) and len(faces(adj, R)) == want

cnt = 0; empty = 0; bad = []; mut_fail = {"b1swap": 0, "yswap": 0}
for n, es in graphs:
    adj = adjacency(n, es)
    for x, y in es + [(b, a) for a, b in es]:
        cadj = contract(n, es, x, y)
        verts = [u for u in cadj if u != y]
        cadj2 = {u: cadj[u] for u in verts}
        rs = rotations(cadj2, verts, cap=50_000)
        if rs is None: continue
        for r in rs:
            if not euler_ok(cadj2, verts, r): continue
            nb = cyc(r[x], cadj2[x][0]) if cadj2[x] else []
            word = "".join("B" if (u in adj[x] and u in adj[y]) else ("X" if u in adj[x] else "Y")
                           for u in nb)
            parse = interval_parse(word)
            if parse is None: continue
            cnt += 1; empty += not word
            if not surgery_ok(adj, cadj2, r, x, y, nb, parse, word):
                bad.append((n, es, x, y, word))
            for v in mut_fail:
                if not surgery_ok(adj, cadj2, r, x, y, nb, parse, word, v): mut_fail[v] += 1
report("[S-수술] 증명의 수술이 종수 0 회전 체계를 만들고 면 순환이 |B|개(빈 단어는 1개) 는다", not bad,
       f"({cnt}개 경우, 그중 빈 단어 {empty}개, 반례 {bad[:2]})")

# [S-수술-음성] 수술의 방향을 바꾸면 반례가 나온다 (위 검사가 방향을 실제로 가린다).
report("[S-수술-음성] b1 순서나 y 둘레의 b1, b2를 바꾸면 반례", all(v > 0 for v in mut_fail.values()),
       f"(b1 순서 변이 반례 {mut_fail['b1swap']}개, y 둘레 변이 반례 {mut_fail['yswap']}개)")

# [cyclic≡S] 이웃만 남긴 순환 단어에서 [cyclic]의 (a)와 [S]의 구간 조건은 같은 조건이다.
cnt = 0; bad = []
for n in range(2, 10):
    for word in itertools.product("XYB", repeat=n):
        if sum(c in "XB" for c in word) < 2 or sum(c in "YB" for c in word) < 2: continue
        cnt += 1
        a, _, _ = cyclic_case(word)
        if a != interval_ok("".join(word)): bad.append("".join(word))
report("[cyclic≡S] 경우 (a) = 꼭짓점 나누기의 구간 조건", not bad, f"({cnt}개 단어, 반례 {bad[:3]})")

# [T] 지지 집합이 5개 이상인 3-연결 그래프에는 수축해도 3-연결인 변이 있다 (Thomassen).
# 연결도는 지지 집합 기준이다 (def:conn3). 수축 뒤 y는 고립점이 되어 지지 집합에서 빠진다.
cnt = 0; bad = []
for n, es in graphs:
    adj = adjacency(n, es)
    if len(support(adj)) < 5 or not k_connected(adj, 3): continue
    cnt += 1
    good = False
    for x, y in es:
        if k_connected(contract(n, es, x, y), 3): good = True; break
    if not good: bad.append((n, es))
report("[T] 수축 가능한 변이 있다", not bad, f"({cnt}개 그래프)")

print("ALL OK" if ok else "MISMATCH")
sys.exit(0 if ok else 1)
