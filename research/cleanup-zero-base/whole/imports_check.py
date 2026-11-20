"""使っていない import の候補を、採取（dump_all.lean の出力）から機械的に出す。使い方：python3 imports_check.py <dump/> <出力.csv>
本体のモジュールどうしの直接の import（M → I）を三つに分ける：
- 使っている：M の宣言（自動生成を含む）の主張か本体が、I が所有する定数を使う。
- 間接だけ：I の定数は使わないが、I を通してしか届かないモジュールの定数を使う（I を外すなら、そのモジュールを直接 import する）。
- 候補：I の定数も、I を通してしか届かないモジュールの定数も使わない。
限界：定数の依存だけを見る。記法・マクロ・属性（@[cite] など）・simp の集合・instance の優先度・open のように、項に定数として現れない使い方は「使っていない」に見える。
M が I を再公開（public import）していて、M を import する側が I を当てにしている場合もある。候補は、実際に外して建てて確かめること。Mathlib など本体の外への import は見ていない。"""
import sys, glob, collections, csv
D, OUT = sys.argv[1], sys.argv[2]
imp = {}; owner = {}
for f in glob.glob(D + '/*.modules.tsv'):
    for l in open(f, encoding='utf-8'):
        a = l.rstrip('\n').split('\t'); imp[a[0]] = set(a[1].split()) if len(a) > 1 and a[1] else set()
for m in {d for ds in imp.values() for d in ds}: imp.setdefault(m, set())
for f in sorted(glob.glob(D + '/*.decls.tsv')):
    for l in open(f, encoding='utf-8'):
        a = l.split('\t', 3); owner.setdefault(a[0], a[2])
uses = collections.defaultdict(collections.Counter); seen = set()
for f in sorted(glob.glob(D + '/*.deps.tsv')):
    for l in open(f, encoding='utf-8'):
        a = l.rstrip('\n').split('\t')
        if a[0] in seen or a[0] not in owner: continue
        seen.add(a[0]); m = owner[a[0]]
        for d in set((a[1].split() if len(a) > 1 else []) + (a[2].split() if len(a) > 2 else [])):
            o = owner.get(d)
            if o and o != m: uses[m][o] += 1
# 位相順とビット集合で、各モジュールから届くモジュールの集合
idx = {m: i for i, m in enumerate(imp)}; rev = collections.defaultdict(set)
for m, ds in imp.items():
    for d in ds: rev[d].add(m)
def closures(graph):
    indeg = {m: len(graph[m]) for m in graph}; st = [m for m, k in indeg.items() if k == 0]; order = []
    r = collections.defaultdict(set)
    for m, ds in graph.items():
        for d in ds: r[d].add(m)
    while st:
        x = st.pop(); order.append(x)
        for u in r[x]:
            indeg[u] -= 1
            if indeg[u] == 0: st.append(u)
    up = {}
    for m in order:
        b = 0
        for d in graph[m]: b |= up.get(d, 0) | (1 << idx[d])
        up[m] = b
    down = {}
    for m in reversed(order):
        b = 0
        for u in r[m]: b |= down.get(u, 0) | (1 << idx[u])
        down[m] = b
    for m in graph: up.setdefault(m, 0); down.setdefault(m, 0)   # 同名の宣言が二つのモジュールにあると、使用の辺に循環が出る。その節は 0 とする
    return up, down
up, down = closures(imp)
ndecl = collections.Counter(owner.values())
rows = []; cls = collections.Counter()
for m, ds in imp.items():
    used = set(uses[m]); usedbits = 0
    for o in used: usedbits |= 1 << idx[o]
    for i in ds:
        if i in used: cls['使っている'] += 1; continue
        others = 0
        for j in ds:
            if j != i: others |= up[j] | (1 << idx[j])
        only_via = (up[i] & usedbits) & ~others
        if only_via:
            via = [x for x in used if (only_via >> idx[x]) & 1]
            cls['間接だけ'] += 1; rows.append([m, i, '間接だけ', len(via), ' '.join(sorted(via)[:6])])
        else:
            k = '候補（宣言のないまとめ用のファイル）' if ndecl[m] == 0 else '候補'
            cls[k] += 1; rows.append([m, i, k, 0, ''])
with open(OUT, 'w', encoding='utf-8') as f:
    w = csv.writer(f); w.writerow(['module', 'import', 'class', 'modules_needed_through_it', 'examples']); w.writerows(sorted(rows))
print('modules', len(imp), 'direct project imports', sum(len(v) for v in imp.values()), dict(cls))
# 建て直しの範囲：今の import と、「実際に使うモジュールだけを import する」場合の比較
need = {m: {o for o in uses[m] if o in imp} for m in imp}
_, down2 = closures(need)
def stats(dn):
    v = sorted(bin(b).count('1') for b in dn.values()); n = len(v)
    return dict(median=v[n // 2], mean=round(sum(v) / n), p90=v[int(n * .9)], p99=v[int(n * .99)], max=v[-1], over1000=sum(1 for x in v if x > 1000), over10000=sum(1 for x in v if x > 10000))
print('downstream now      ', stats(down)); print('downstream if minimal', stats(down2))
c = collections.Counter(r[1] for r in rows if r[2] == '候補')
print('most often an unused candidate:', [(k.replace('SerrePositivity.', ''), v) for k, v in c.most_common(10)])
gain = sorted(((bin(down[m]).count('1') - bin(down2.get(m, 0)).count('1'), m) for m in imp), reverse=True)[:8]
print('largest drop in downstream:', [(m.replace('SerrePositivity.', '')[-60:], bin(down[m]).count('1'), bin(down2.get(m, 0)).count('1')) for g, m in gain])
mods_with = len({r[0] for r in rows if r[2] == '候補'}); print('modules with at least one candidate', mods_with, '| modules without declarations', sum(1 for m in imp if ndecl[m] == 0))
per = collections.Counter(r[0] for r in rows if r[2] == '候補'); v = sorted(per.values()); print('candidates per module: median', v[len(v)//2], 'max', v[-1], [(m.replace('SerrePositivity.', '')[-50:], k) for m, k in per.most_common(5)])
top = collections.Counter('.'.join(r[0].split('.')[1:3]) for r in rows if r[2] == '候補'); print('by area:', top.most_common(12))
