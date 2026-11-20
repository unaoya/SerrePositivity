"""幹の規則（trunk.py）で全宣言を概念に割り当てる。使い方：python3 assign.py <W.pkl> <cand.pkl> <X.pkl> <読んだ核の pickle の列> <出力の接頭辞>
核は、読んだ定義（上位 320 個と、未割り当ての型に多い 260 個）だけ。割り当ては：核そのもの → 型に核が直接現れる（最も下流）→ 型に現れる本体の定義をたどる
→ 型に現れる Mathlib の定義（MATHLIB_ROOTS の順）→ 本体をたどる → 未割り当て。"""
import pickle, re, sys, collections, csv, os
sys.path.insert(0, os.path.dirname(__file__)); from trunk import RULES, RULES2, RULES3, RULES4, MATHLIB_ROOTS, MATHLIB_ROOTS3, RENAME, PROMOTE
import json, glob
W = pickle.load(open(sys.argv[1], 'rb')); N = W['N']; cand, tus = pickle.load(open(sys.argv[2], 'rb')); xn, X = pickle.load(open(sys.argv[3], 'rb'))
hubs = []
for f in sys.argv[4].split(','): hubs += pickle.load(open(f, 'rb'))
R = [(c, re.compile(p)) for c, p in RULES4 + RULES3 + RULES2 + RULES]; MR = [(c, re.compile(p)) for c, p in MATHLIB_ROOTS3 + MATHLIB_ROOTS]
def lab(n):
    # Kerodon の章の名前空間（FibrationsOfInfinityCategories など）は広すぎるので、規則に当てる前に外す。節の名前空間は残す
    n = re.sub(r'InfinityCategories\.Kerodon\.[A-Za-z]+\.', 'Kerodon.', n)
    for c, p in R:
        if p.search(n): return c
L = {h: lab(N[h]['name']) for h in hubs}; nolab = [N[h]['name'] for h in hubs if L[h] is None]; L = {h: c for h, c in L.items() if c}
# 名前で広げた核：読んでいないが、型に 15 回以上現れ、名前が規則に当たる定義
read = set(L); ext_hubs = 0
for h in cand:
    if h not in L and tus[h] >= 15:
        c = lab(N[h]['name'])
        if c: L[h] = c; ext_hubs += 1
print('read hubs', len(read), 'hubs extended by name', ext_hubs)
xlab = {}
for q, n in xn.items():
    for i, (c, p) in enumerate(MR):
        if p.search(n): xlab[q] = (i, c); break
# 読む作業の結果（split/c*.json）で上書きする：読んだ定義は、読んだ結果の概念と小概念に入れる
strip = lambda n: re.sub(r'^_private\..*?\.0\.', '', n)
byname = {}
for h, d in N.items(): byname.setdefault(strip(d['name']), h)
SUB = {}; MRULES = {}; DESC = {}; moved = 0; unknown = []
norm = lambda c: RENAME.get(c, c); UNC = set()
for f in sorted(glob.glob(os.path.join(os.path.dirname(__file__), 'split', 'c*.json'))) + sorted(glob.glob(os.path.join(os.path.dirname(__file__), 'split2', 'd*.json'))):
    j = json.load(open(f, encoding='utf-8')); c0 = j['concept']
    for sc in j['subconcepts']: DESC[(c0, sc['name'])] = sc
    if j.get('mathlib_rules'): MRULES[c0] = [(re.compile(r), n) for r, n in j['mathlib_rules']]
    for n in j.get('uncertain', []):
        if n in byname: UNC.add(byname[n])
    for n, v in j['assign'].items():
        h = byname.get(n)
        if h is None: unknown.append(n); continue
        if v.startswith('MOVE:'):
            t = v[5:].strip()
            if t and t != '?': L[h] = t; SUB[h] = '（読んで移した定義）'; moved += 1
            else: L[h] = c0; SUB[h] = '（行き先の決まらない定義）'
        else:
            c = c0
            for a0, pre, b0 in PROMOTE:
                if norm(a0) == norm(c0) and v.startswith(pre): c = b0
            L[h] = c; SUB[h] = v
            if c != c0: DESC[(c, v)] = DESC[(c0, v)]
print('read assignments applied', len(SUB), 'moved', moved, 'unknown names', len(unknown), unknown[:5])
indeg = {h: len(d['tdeps']) + len(d['vdeps']) for h, d in N.items()}
order = []; st = [h for h, k in indeg.items() if k == 0]
while st:
    x = st.pop(); order.append(x)
    for u in N[x]['users']:
        indeg[u] -= 1
        if indeg[u] == 0: st.append(u)
depth = {}; src = {}; con = {}; how = {}; sub = {}
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
    cs = [(depth[q], con[q]) for q in t if con.get(q) and q in cand]
    if cs: src[x] = None; con[x] = max(cs)[1]; how[x] = '型の定義の概念'; continue
    xs = [xlab[q] for q in X.get(x, ()) if q in xlab]
    if xs:
        src[x] = None; con[x] = min(xs)[1]; how[x] = 'Mathlib の定義'
        if con[x] in MRULES:
            names = [xn[q] for q in X.get(x, ())]; best = None
            for i, (r, nm) in enumerate(MRULES[con[x]]):
                if any(r.search(n0) for n0 in names): best = nm; break
            sub[x] = best or '（その他）'
        continue
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
for x in N:
    if x in sub: continue
    h = src.get(x)
    sub[x] = SUB.get(h, '（まだ読んでいない定義）') if h is not None else ('（Mathlib の定義だけの主張）' if how[x] == 'Mathlib の定義' else '（その他）')
    if con[x] and (con[x], sub[x]) not in DESC and h is not None and h in SUB and SUB[h].startswith('（読んで移'): pass
con = {x: (RENAME.get(c, c) if c else c) for x, c in con.items()}
T2 = collections.defaultdict(collections.Counter)
for x, d in N.items():
    k = T2[(con[x] or '（未割り当て）/（未割り当て）', sub[x])]; k['decls'] += 1; k['uncertain'] += (src.get(x) in UNC); k['lines'] += d['lines']; k['layer%d' % d['layer']] += 1; k[d['K']] += 1
pre = sys.argv[5]
with open(pre + '.csv', 'w', encoding='utf-8') as f:
    w = csv.writer(f); cols = ['decls', 'lines', 'layer1', 'layer2', 'layer3', 'layer4'] + KS + ['核', '型に核', '型の定義をたどる', '型の定義の概念', 'Mathlib の定義', '本体をたどる']
    w.writerow(['group', 'concept'] + cols)
    for c in sorted(T): w.writerow(c.split('/', 1) + [T[c][k] for k in cols])
with open(pre + '-sub.csv', 'w', encoding='utf-8') as f:
    w = csv.writer(f); cols2 = ['decls', 'lines', 'layer1', 'layer2', 'layer3', 'layer4'] + KS + ['uncertain']
    w.writerow(['group', 'concept', 'subconcept', 'description', 'reference'] + cols2)
    inv = {v: k for k, v in RENAME.items()}
    for (c, sb) in sorted(T2):
        dsc = DESC.get((inv.get(c, c), sb)) or DESC.get((c, sb)) or {}
        w.writerow(c.split('/', 1) + [sb, dsc.get('description', ''), dsc.get('reference', '')] + [T2[(c, sb)][k] for k in cols2])
pickle.dump(dict(L=L, src=src, con=con, how=how, depth=depth, sub=sub, SUB=SUB), open(sys.argv[6], 'wb'))
G = collections.defaultdict(collections.Counter)
for c, k in T.items():
    for a, b in k.items(): G[c.split('/')[0]][a] += b
for g in sorted(G): print(g, '|', len([c for c in T if c.startswith(g + '/')]), '|', G[g]['decls'], '|', G[g]['lines'], '|', G[g]['layer1'], G[g]['layer2'], G[g]['layer3'], G[g]['layer4'])
