"""大きい概念ごとに、中の核（定義）の一覧と、型に現れる Mathlib の定義の一覧を出す（二段目に分けるための読む材料）。
使い方：python3 split_lists.py <W.pkl> <cand.pkl> <X.pkl> <trunk.pkl> <出力ディレクトリ> <最小の宣言数>"""
import pickle, collections, re, csv, json, sys
W = pickle.load(open(sys.argv[1], 'rb')); N = W['N']; cand, tus = pickle.load(open(sys.argv[2], 'rb')); xn, X = pickle.load(open(sys.argv[3], 'rb')); T = pickle.load(open(sys.argv[4], 'rb'))
OUT = sys.argv[5]; MIN = int(sys.argv[6]); con = T['con']; src = T['src']; srcs = {}
def doc(d):
    f = d['mod'].replace('.', '/') + '.lean'
    if f not in srcs: srcs[f] = open(f, encoding='utf-8').read().split('\n')
    t = ' '.join(srcs[f][d['line'] - 1:d['end']]); m = re.search(r'/--(.*?)-/', t)
    sig = re.sub(r'/--.*?-/', '', t); sig = re.sub(r'@\[[^\]]*\]\s*', '', sig); sig = re.sub(r'_root_\.SerrePositivity\.[A-Za-z0-9_.]*\.', '', sig)
    return (m.group(1).strip() if m else '')[:160], re.sub(r'\s+', ' ', sig).strip()[:200]
size = collections.Counter(c for c in con.values() if c); bysrc = collections.defaultdict(collections.Counter)
for x, s in src.items():
    if s is not None and con[x]: bysrc[con[x]][s] += 1
idx = []
for c, n in size.most_common():
    if n < MIN: break
    key = 'c%02d' % len(idx); hubs = bysrc[c].most_common(170)
    with open(f'{OUT}/{key}.csv', 'w', encoding='utf-8') as f:
        w = csv.writer(f); w.writerow(['definition', 'declarations_assigned', 'type_users', 'docstring', 'signature', 'file', 'line'])
        for h, k in hubs:
            d = N[h]; dd, sig = doc(d); w.writerow([re.sub(r'^_private\..*?\.0\.', '', d['name']), k, tus.get(h, 0), dd, sig, d['mod'].replace('.', '/') + '.lean', d['line']])
    M = [x for x in N if con[x] == c and src[x] is None]; ext = collections.Counter()
    for x in M:
        for q in X.get(x, ()): ext[q] += 1
    with open(f'{OUT}/{key}.mathlib.txt', 'w', encoding='utf-8') as f:
        f.write(f'# {len(M)} declarations of this concept have no project definition in their statement. Mathlib constants in their statements (count):\n')
        for q, k in ext.most_common(160): f.write(f'{xn[q]}\t{k}\n')
    idx.append(dict(key=key, concept=c, decls=n, hubs=len(bysrc[c]), listed=len(hubs), covered=sum(k for _, k in hubs), mathlib_only=len(M)))
json.dump(idx, open(f'{OUT}/index.json', 'w'), ensure_ascii=False, indent=1)
for i in idx: print(i)
