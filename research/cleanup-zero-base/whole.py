"""全体の採取（dump_all.lean の出力）を畳んで、宣言ごとの種類と四つの層を付ける。
使い方：python3 research/cleanup-zero-base/whole.py <dump_all の出力ディレクトリ> <結果の pickle>
畳み方：ソース上の範囲を持つ定数を、同じモジュールの中で範囲が入れ子になっていれば外側へ寄せ、範囲のない定数（自動生成）は名前の接頭辞で親へ寄せる。
層：1 主定理（SerrePositivity.main_statement）が使う／2 対応表が名指しする宣言とそれが使うもの／3 root から届くがどちらでもない／4 root から届かない。
種類：未使用・言い換え・結果・再利用の補題・分割の補題（kinds.py と同じ基準。機械の初期値）。"""
import sys, os, re, glob, csv, pickle, collections
D, OUT = sys.argv[1], sys.argv[2]
csv.field_size_limit(10**9)
C = {}; rootmods = set(); mods = {}
for f in sorted(glob.glob(D + '/*.modules.tsv')):
    isroot = os.path.basename(f).startswith('root.')
    for l in open(f, encoding='utf-8'):
        a = l.rstrip('\n').split('\t'); mods[a[0]] = a[1].split() if len(a) > 1 and a[1] else []
        if isroot: rootmods.add(a[0])
for f in sorted(glob.glob(D + '/*.decls.tsv')):
    for l in open(f, encoding='utf-8'):
        a = l.rstrip('\n').split('\t')
        if a[0] in C: continue
        C[a[0]] = dict(name=a[1], mod=a[2], kind=a[3], inst=a[4] == '1', prop=a[5] == '1', line=int(a[6]), end=int(a[7]),
                       internal=a[8] == '1', doc=int(a[9]), hasval=a[10] == '1', xt=int(a[11]), xv=int(a[12]), t=(), v=())
for f in sorted(glob.glob(D + '/*.deps.tsv')):
    for l in open(f, encoding='utf-8'):
        a = l.rstrip('\n').split('\t')
        c = C.get(a[0])
        if c is None or c['t'] or c['v']: continue
        c['t'] = tuple(a[1].split()) if len(a) > 1 and a[1] else (); c['v'] = tuple(a[2].split()) if len(a) > 2 and a[2] else ()
byname = {c['name']: h for h, c in C.items()}
print('constants', len(C), 'modules', len(mods), 'root modules', len(rootmods), flush=True)
# 畳む
def user(n):
    m = re.match(r'_private\.(?:.*?)\.0\.(.*)$', n); return m.group(1) if m else n
def is_private_source(n):
    # private な宣言は内部名の扱いになるが、ソースに書いた宣言。記法・マクロの補助（_aux_…、unexpand、term…）は除く
    if not n.startswith('_private.'): return False
    u = user(n)
    return not any(x.startswith('_') or x.startswith('term') or x.startswith('«') for x in u.split('.')) and 'unexpand' not in u
parent = {}
bymod = collections.defaultdict(list)
for h, c in C.items():
    if c['line'] > 0 and (not c['internal'] or is_private_source(c['name'])): bymod[c['mod']].append(h)
for m, hs in bymod.items():
    hs.sort(key=lambda h: (C[h]['line'], -C[h]['end'], len(C[h]['name'])))
    stack = []
    for h in hs:
        c = C[h]
        while stack and C[stack[-1]]['end'] < c['line']: stack.pop()
        if stack and C[stack[-1]]['end'] >= c['end']: parent[h] = stack[0]   # 入れ子（構造体の射影、同じ範囲の生成物）
        else: stack = [h]
src = {h for hs in bymod.values() for h in hs if h not in parent}
uname = collections.defaultdict(list)
for h in src: uname[user(C[h]['name'])].append(h)
def owner(h):
    if h in src: return h
    if h in parent: return parent[h]
    n = user(C[h]['name']); m = C[h]['mod']
    while '.' in n:
        n = n.rsplit('.', 1)[0]
        for q in uname.get(n, ()):
            if C[q]['mod'] == m: return q
        if n.endswith('_assoc') or n.endswith('_apply'): pass
    return None
own = {}; orphan = 0
for h in C:
    o = owner(h); own[h] = o
    if o is None: orphan += 1
print('source declarations', len(src), 'folded', len(C) - len(src) - orphan, 'orphans', orphan, flush=True)
N = {h: dict(C[h], tdeps=set(), vdeps=set(), users=set(), gen=0) for h in src}
for h, c in C.items():
    o = own[h]
    if o is None: continue
    if o != h: N[o]['gen'] += 1; N[o]['xv'] += c['xt'] + c['xv']
    for k, key in ((c['t'], 'tdeps' if o == h else 'vdeps'), (c['v'], 'vdeps')):
        for d in k:
            q = own.get(d)
            if q and q != o: N[o][key].add(q)
for h, d in N.items():
    d['vdeps'] -= d['tdeps']
    for q in d['tdeps'] | d['vdeps']: N[q]['users'].add(h)
# 対応表の名指し
named = set(); tok_total = 0; tok_hit = 0
suffix = collections.defaultdict(list)
for h in src:
    n = C[h]['name']; p = n.split('.')
    for i in range(1, len(p)): suffix['.'.join(p[i:])].append(h)
for f in glob.glob('research/*-coverage/**/*.csv', recursive=True):
    try: rows = list(csv.DictReader(open(f, encoding='utf-8')))
    except Exception: continue
    for r in rows:
        for k, v in r.items():
            if k and 'declaration' in k and v:
                for e in v.split(' | '):
                    t = e.split(' @ ')[0].strip().strip('`')
                    if not t or t.startswith('Mathlib') : continue
                    tok_total += 1
                    hs = [byname[t]] if t in byname else suffix.get(t, [])
                    hs = [own[x] for x in hs if own.get(x)]
                    if len(set(hs)) == 1: named.add(hs[0]); tok_hit += 1
print('coverage tokens', tok_total, 'resolved', tok_hit, 'named declarations', len(named), flush=True)
def closure(seeds):
    seen = set(seeds); st = list(seeds)
    while st:
        x = st.pop()
        for q in N[x]['tdeps'] | N[x]['vdeps']:
            if q not in seen: seen.add(q); st.append(q)
    return seen
main = own[byname['SerrePositivity.main_statement']]
L1 = closure([main]); L2 = closure(named) - L1
for h, d in N.items():
    d['layer'] = 1 if h in L1 else 2 if h in L2 else 3 if d['mod'] in rootmods else 4
    d['named'] = h in named
# 種類
srcs = {}
def body(d):
    f = d['mod'].replace('.', '/') + '.lean'
    if f not in srcs:
        try: srcs[f] = open(f, encoding='utf-8').read().split('\n')
        except Exception: srcs[f] = []
    return '\n'.join(srcs[f][d['line'] - 1:d['end']])
for h, d in N.items():
    b = body(d); d['lines'] = d['end'] - d['line'] + 1; d['chars'] = len(b)
    tail = b.split(':=')[-1].strip() if ':=' in b else ''
    thm = d['kind'] == 'thm'
    para = (thm and (re.fullmatch(r'(by\s+)?rfl', tail) or ('\n' not in tail and len(tail) < 200 and not tail.startswith('by') and tail != ''))) or \
           (not thm and d['kind'] == 'def' and '\n' not in tail and len(tail) < 200 and 'where' not in b and tail != '')
    xm = {N[q]['mod'].split('.')[1] for q in d['users']} - {d['mod'].split('.')[1]}
    n = len(d['users'])
    d['K'] = '未使用' if (n == 0 and not d['named'] and h != main) else '言い換え' if para else '結果' if (d['named'] or h == main) else \
             '再利用' if n >= 2 else '分割'
    d['xtop'] = len(xm)
pickle.dump(dict(N=N, mods=mods, rootmods=rootmods, main=main), open(OUT, 'wb'))
tot = collections.Counter(); ln = collections.Counter()
for d in N.values(): tot[(d['layer'], d['K'])] += 1; ln[(d['layer'], d['K'])] += d['lines']
KS = ['結果', '再利用', '分割', '言い換え', '未使用']
print('layer | ' + ' | '.join(KS) + ' | 計（宣言／行）')
for l in (1, 2, 3, 4):
    print(l, '|', ' | '.join(f"{tot[(l,k)]}/{ln[(l,k)]}" for k in KS), '|', sum(tot[(l, k)] for k in KS), '/', sum(ln[(l, k)] for k in KS))
