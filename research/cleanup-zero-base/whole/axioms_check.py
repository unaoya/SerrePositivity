"""全宣言の公理と sorry の状態（監査のゼロからの設計の G2、試作）。使い方：python3 axioms_check.py <採取のディレクトリ dump/> [出力.csv]
採取（dump_all.lean）の deps の辺をたどり、各定数が推移的に依る公理を計算する。本体の外の定数は、許可した公理だけに依ると仮定する。"""
import sys, glob, collections, csv
D = sys.argv[1]; ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
C = {}; deps = {}; direct = collections.defaultdict(set); rootmods = set()
for f in glob.glob(D + '/root.modules.tsv'):
    for l in open(f, encoding='utf-8'): rootmods.add(l.split('\t')[0])
for f in sorted(glob.glob(D + '/*.decls.tsv')):
    for l in open(f, encoding='utf-8'):
        a = l.rstrip('\n').split('\t'); C.setdefault(a[0], (a[1], a[2], a[3]))
for f in sorted(glob.glob(D + '/*.deps.tsv')):
    for l in open(f, encoding='utf-8'):
        a = l.rstrip('\n').split('\t')
        if a[0] not in deps: deps[a[0]] = set((a[1].split() if len(a) > 1 else []) + (a[2].split() if len(a) > 2 else []))
for f in sorted(glob.glob(D + '/*.axioms.tsv')):
    for l in open(f, encoding='utf-8'):
        a = l.rstrip('\n').split('\t'); direct[a[0]] |= set(a[1].split())
        if a[2] == 'axiom': direct[a[0]].add(C[a[0]][0])
users = collections.defaultdict(set)
for h, ds in deps.items():
    for d in ds: users[d].add(h)
# 許可しない公理ごとに、依る定数の集合を広げる
bad = collections.defaultdict(set)
for h, axs in direct.items():
    for ax in axs - ALLOWED: bad[ax].add(h)
closure = {}
for ax, seeds in bad.items():
    seen = set(seeds); st = list(seeds)
    while st:
        x = st.pop()
        for u in users.get(x, ()):
            if u not in seen: seen.add(u); st.append(u)
    closure[ax] = seen
import subprocess, os
tracked = [f[:-5].replace('/', '.') for f in subprocess.run(['git', 'ls-files', 'SerrePositivity', 'SerrePositivity.lean'], capture_output=True, text=True).stdout.split() if f.endswith('.lean') and '/Archive/' not in f]
dumped = set()
for f in glob.glob(D + '/*.modules.tsv'):
    for l in open(f, encoding='utf-8'): dumped.add(l.split('\t')[0])
notdumped = sorted(set(tracked) - dumped)
print('tracked modules', len(tracked), 'dumped', len(dumped & set(tracked)), 'NOT DUMPED', len(notdumped))
if notdumped: print('  ** 全宣言ではない。採取されていないモジュール：', ' '.join(m.replace('SerrePositivity.', '') for m in notdumped[:25]))
print('constants', len(C), 'in root closure', sum(1 for h in C if C[h][1] in rootmods))
print('directly used axioms:', dict(collections.Counter(ax for axs in direct.values() for ax in axs)))
for ax, seen in closure.items():
    print(f'\n{ax}: direct {len(bad[ax])}, transitive {len(seen)} (in root closure {sum(1 for h in seen if C[h][1] in rootmods)}, outside {sum(1 for h in seen if C[h][1] not in rootmods)})')
    for h in sorted(bad[ax], key=lambda h: C[h][0]): print('  direct:', C[h][0], '|', C[h][1], '| dependents', len({x for x in closure[ax]}) if len(bad[ax]) == 1 else '')
    top = collections.Counter('.'.join(C[h][1].split('.')[1:3]) for h in seen); print('  by area:', top.most_common(10))
if len(sys.argv) > 2:
    with open(sys.argv[2], 'w', encoding='utf-8') as f:
        w = csv.writer(f); w.writerow(['axiom', 'constant', 'module', 'kind', 'direct'])
        for ax, seen in closure.items():
            for h in sorted(seen, key=lambda h: C[h][0]): w.writerow([ax, C[h][0], C[h][1], C[h][2], int(h in bad[ax])])
