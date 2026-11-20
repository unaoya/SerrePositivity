"""概念どうしの依存を、宣言の主張（型）の依存から出す。使い方：python3 concept_deps.py <W.pkl> <trunk.pkl> <出力.csv>
A → B の重み = A の宣言のうち、主張に B の宣言（定義）を含むものの数。A の宣言数に対する割合も出す。"""
import pickle, collections, csv, sys
W = pickle.load(open(sys.argv[1], 'rb')); N = W['N']; T = pickle.load(open(sys.argv[2], 'rb')); con = T['con']
size = collections.Counter(c for c in con.values() if c); E = collections.Counter()
for x, d in N.items():
    a = con.get(x)
    if not a: continue
    for b in {con.get(q) for q in d['tdeps']} - {a, None}: E[(a, b)] += 1
with open(sys.argv[3], 'w', encoding='utf-8') as f:
    w = csv.writer(f); w.writerow(['from', 'to', 'declarations', 'share_of_from'])
    for (a, b), k in sorted(E.items(), key=lambda kv: -kv[1]):
        if k >= 20: w.writerow([a, b, k, f'{k / size[a]:.3f}'])
# 層：強い依存（A の 8% 以上が B を主張に含む）だけで向きを見る
strong = collections.defaultdict(set)
for (a, b), k in E.items():
    if k / size[a] >= 0.08 and E[(a, b)] / size[a] > 2 * E.get((b, a), 0) / size[b]: strong[a].add(b)
level = {}
def lv(a, seen=()):
    if a in level: return level[a]
    if a in seen: return 0
    level[a] = 1 + max([lv(b, seen + (a,)) for b in strong[a]], default=-1); return level[a]
for a in size: lv(a)
by = collections.defaultdict(list)
for a, l in level.items(): by[l].append(a)
for l in sorted(by): print(l, ' | '.join(sorted(x.split('/')[1] for x in by[l])))
print('--- 各概念が主に依る概念（上位 3）')
for a in sorted(size, key=lambda a: -size[a])[:30]:
    top = sorted(((k, b) for (a2, b), k in E.items() if a2 == a), reverse=True)[:3]
    print(a.split('/')[1], size[a], '←', ', '.join(f"{b.split('/')[1]} {k / size[a] * 100:.0f}%" for k, b in top))
pickle.dump(dict(E=E, level=level, strong={a: sorted(b) for a, b in strong.items()}), open(sys.argv[3] + '.pkl', 'wb'))
