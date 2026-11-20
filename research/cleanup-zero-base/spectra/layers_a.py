#!/usr/bin/env python3
"""対称スペクトルの下の一般論（A1 加群、A2 豊穣、A3 対称列）の宣言の表。
  python3 research/cleanup-zero-base/spectra/layers_a.py <概念の木の作業ディレクトリ> <出力 csv>
主張（型）の依存を推移的にたどり、何を使って述べられているかで分ける（名前・ファイルでは決めない）：
  スペクトル用：テンソル冪の列・球面の列（Sym(K)）に依存
  対称列：対称列の圏（SymmetricSequence）に依存
  圏論一般：どちらにも依存しない
使う側は、領域ごと（A1/A2/A3/B/C/モデル・安定/スペクトルの外）に数える。"""
import sys, pickle, csv, collections, re
WORK, OUT = sys.argv[1], sys.argv[2]
W = pickle.load(open(WORK + '/W.pkl', 'rb')); N = W['N']; T = pickle.load(open(WORK + '/tree.pkl', 'rb'))
P = 'SerrePositivity.'
def area(m):
    m = m[len(P):] if m.startswith(P) else m
    if m.startswith('CategoryTheory.Monoidal.Mod'): return 'A1'
    if m.startswith('CategoryTheory.Enriched'): return 'A2'
    if m.startswith('Spectra.SymmetricSequence'): return 'A3'
    if m.startswith('Spectra.General'): return 'B'
    if m.startswith('Spectra.SymmetricSpectrum'): return 'C'
    if m.startswith('Spectra.ModelCategory') or m.startswith('Spectra.Stable'): return '利用側'
    if m.startswith('Spectra.Pointed'): return '基点付き'
    if m.startswith('Spectra'): return 'Spectra他'
    if m.startswith('CategoryTheory'): return 'CT他'
    return '外'
name = {x: d['name'] for x, d in N.items()}
strip = lambda n: re.sub(r'^_private\..*?\.0\.', '', n)
# 目印になる定義
seq = {x for x, d in N.items() if strip(d['name']) in ('SerrePositivity.SymmetricSequence',)}
sph = {x for x, d in N.items() if strip(d['name']).split('.')[-1] in ('tensorPowerSequence', 'sphereSequence') and area(d['mod']) == 'A3'}
print('markers', [name[x] for x in seq], [name[x] for x in sph])
memo = {}
def reach(x):
    # 型の依存の推移閉包（定義は型と値、定理は型だけ）に目印があるか
    if x in memo: return memo[x]
    memo[x] = (False, False); st = [x]; seen = {x}; a = b = False
    while st:
        y = st.pop(); d = N.get(y)
        if d is None: continue
        if y in seq: a = True
        if y in sph: b = True
        if a and b: break
        ds = set(d['tdeps']) if (y == x or d['kind'] == 'thm') else set(d['tdeps']) | set(d.get('vdeps', ()))
        if y == x and d['kind'] != 'thm': ds |= set(d.get('vdeps', ()))
        for z in ds:
            if z not in seen: seen.add(z); st.append(z)
    memo[x] = (a, b); return memo[x]
rows = []
for x, d in N.items():
    ar = area(d['mod'])
    if ar not in ('A1', 'A2', 'A3'): continue
    a, b = reach(x)
    cls = 'スペクトル用' if b else '対称列' if a else '圏論一般'
    uc = collections.Counter(area(N[u]['mod']) for u in d['users'] if u in N)
    rows.append({'area': ar, 'module': d['mod'][len(P):], 'declaration': strip(d['name']), 'kind': d['kind'], 'statement_uses': cls,
                 'lines': d['lines'], 'K': d['K'], 'concept': T['con'].get(x, ''), 'sub': T['sub'].get(x, ''),
                 'users_total': sum(uc.values()), **{'users_' + k: uc.get(k, 0) for k in ('A1', 'A2', 'A3', 'B', 'C', '利用側', '基点付き', 'CT他', '外')}})
rows.sort(key=lambda r: (r['area'], r['module'], r['declaration']))
with open(OUT, 'w', encoding='utf-8', newline='') as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
print(len(rows), 'declarations')
for ar in ('A1', 'A2', 'A3'):
    R = [r for r in rows if r['area'] == ar]
    print(ar, len(R), 'lines', sum(r['lines'] for r in R), dict(collections.Counter(r['statement_uses'] for r in R)), 'unused', sum(r['users_total'] == 0 for r in R),
          'used outside spectra', sum(r['users_外'] + r['users_CT他'] > 0 for r in R), dict(collections.Counter(r['K'] for r in R)))
