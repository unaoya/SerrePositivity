"""幹の規則（trunk.py）で全宣言を概念に割り当てる。使い方：python3 assign.py <W.pkl> <cand.pkl> <X.pkl> <読んだ核の pickle の列> <出力の接頭辞>
核は、読んだ定義（上位 320 個と、未割り当ての型に多い 260 個）だけ。割り当ては：核そのもの → 型に核が直接現れる（最も下流）→ 型に現れる本体の定義をたどる
→ 型に現れる Mathlib の定義（MATHLIB_ROOTS の順）→ 本体をたどる → 未割り当て。"""
import pickle, re, sys, collections, csv, os
sys.path.insert(0, os.path.dirname(__file__)); from trunk import RULES, RULES2, MATHLIB_ROOTS
W = pickle.load(open(sys.argv[1], 'rb')); N = W['N']; cand, tus = pickle.load(open(sys.argv[2], 'rb')); xn, X = pickle.load(open(sys.argv[3], 'rb'))
hubs = []
for f in sys.argv[4].split(','): hubs += pickle.load(open(f, 'rb'))
R = [(c, re.compile(p)) for c, p in RULES2 + RULES]; MR = [(c, re.compile(p)) for c, p in MATHLIB_ROOTS]
def lab(n):
    for c, p in R:
        if p.search(n): return c
L = {h: lab(N[h]['name']) for h in hubs}; nolab = [N[h]['name'] for h in hubs if L[h] is None]; L = {h: c for h, c in L.items() if c}
xlab = {}
for q, n in xn.items():
    for i, (c, p) in enumerate(MR):
        if p.search(n): xlab[q] = (i, c); break
indeg = {h: len(d['tdeps']) + len(d['vdeps']) for h, d in N.items()}
order = []; st = [h for h, k in indeg.items() if k == 0]
while st:
    x = st.pop(); order.append(x)
    for u in N[x]['users']:
        indeg[u] -= 1
        if indeg[u] == 0: st.append(u)
depth = {}; src = {}; con = {}; how = {}
for x in order:
    d = N[x]; t, v = d['tdeps'], d['vdeps']; depth[x] = 1 + max([depth[q] for q in t | v], default=-1)
    if x in L: src[x] = x; con[x] = L[x]; how[x] = '核'; continue
    best = None
    for q in t:
        if q in L and (best is None or depth[q] > depth[best]): best = q
    if best is not None: src[x] = best; con[x] = L[best]; how[x] = '型に核'; continue
    for q in t:
        s = src.get(q)
        if s is not None and (best is None or depth[s] > depth[best]): best = s
    if best is not None: src[x] = best; con[x] = L[best]; how[x] = '型の定義をたどる'; continue
    xs = [xlab[q] for q in X.get(x, ()) if q in xlab]
    if xs: src[x] = None; con[x] = min(xs)[1]; how[x] = 'Mathlib の定義'; continue
    cs = [(depth[src[q]], con[q]) for q in t | v if src.get(q) is not None]
    if cs: src[x] = None; con[x] = max(cs)[1]; how[x] = '本体をたどる'; continue
    cs = [con[q] for q in t | v if con.get(q)]
    if cs: src[x] = None; con[x] = collections.Counter(cs).most_common(1)[0][0]; how[x] = '本体をたどる'; continue
    src[x] = None; con[x] = None; how[x] = '未割り当て'
print('hubs', len(L), 'unlabelled hubs', len(nolab), nolab[:20]); print(collections.Counter(how.values()))
KS = ['結果', '再利用', '分割', '言い換え', '未使用']
T = collections.defaultdict(collections.Counter)
for x, d in N.items():
    c = con[x] or '（未割り当て）/（未割り当て）'; k = T[c]
    k['decls'] += 1; k['lines'] += d['lines']; k['layer%d' % d['layer']] += 1; k[d['K']] += 1; k[how[x]] += 1
pre = sys.argv[5]
with open(pre + '.csv', 'w', encoding='utf-8') as f:
    w = csv.writer(f); cols = ['decls', 'lines', 'layer1', 'layer2', 'layer3', 'layer4'] + KS + ['核', '型に核', '型の定義をたどる', 'Mathlib の定義', '本体をたどる']
    w.writerow(['group', 'concept'] + cols)
    for c in sorted(T): w.writerow(c.split('/', 1) + [T[c][k] for k in cols])
pickle.dump(dict(L=L, src=src, con=con, how=how, depth=depth), open(sys.argv[6], 'wb'))
G = collections.defaultdict(collections.Counter)
for c, k in T.items():
    for a, b in k.items(): G[c.split('/')[0]][a] += b
for g in sorted(G): print(g, '|', len([c for c in T if c.startswith(g + '/')]), '|', G[g]['decls'], '|', G[g]['lines'], '|', G[g]['layer1'], G[g]['layer2'], G[g]['layer3'], G[g]['layer4'])
