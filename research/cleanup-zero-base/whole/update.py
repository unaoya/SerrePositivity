#!/usr/bin/env python3
"""概念の木を作り直す（採取 → 畳む → 割り当て → 表 → ページ）。main の root で、main の .lake が建っている状態で実行する。

  python3 research/cleanup-zero-base/whole/update.py <作業ディレクトリ> [--skip-dump] [--label <版の名前>] [--prev <前回の作業ディレクトリ>]

- 採取（約 20 分、Lean を 5 回起動、鍵 coord）：全モジュールの宣言と依存を出す。一つのプロセスで全部読むと vnode の上限に届くので、root の閉包と残りの塊に分ける。
  `--skip-dump` を付けると、作業ディレクトリの dump/ にある前回の採取を使う（木だけ直したとき）。
- 割り当て（約 10 秒）：読んだ定義の正本 `definitions.csv` と、Mathlib の定義の規則（trunk.py、split/c*.json）、移し替えの表（remap/）から、全宣言を概念に入れる。
- 出力：作業ディレクトリに W.pkl・X.pkl・tree.pkl・tree-sub.csv・tree-order.csv・tree.html・report.txt。
  report.txt には、宣言と定義の数、読んだ定義の数、definitions.csv にあってコードから消えた定義（改名・削除）、前回との差（--prev）を書く。

木を直すとき：`definitions.csv` の行を直す・足す（定義の完全名、概念、小概念、補助、止めた経路）。概念の名前を変えるときは、definitions.csv と remap/remap-*.csv の new_concept の両方を置き換える。その後 `--skip-dump` で実行する。
コードを変えたとき：main に取り込んで建った後、`--skip-dump` なしで実行する。消えた定義は report.txt に出るので、改名なら definitions.csv の名前を直す。"""
import sys, os, subprocess, pickle, glob, collections, csv, re, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
args = sys.argv[1:]; WORK = os.path.abspath(args[0]); SKIP = '--skip-dump' in args
LABEL = args[args.index('--label') + 1] if '--label' in args else time.strftime('%Y-%m-%d')
PREV = os.path.abspath(args[args.index('--prev') + 1]) if '--prev' in args else None
DUMP = os.path.join(WORK, 'dump'); os.makedirs(DUMP, exist_ok=True); os.chdir(ROOT)
def run(cmd, **kw):
    print('+', ' '.join(cmd)[:160], flush=True); r = subprocess.run(cmd, **kw)
    if r.returncode != 0: sys.exit(f'failed: {cmd[:6]}')
    return r
if not SKIP:
    files = [f for f in subprocess.run(['git', 'ls-files', 'SerrePositivity', 'SerrePositivity.lean'], capture_output=True, text=True).stdout.split() if f.endswith('.lean') and '/Archive/' not in f]
    built = [f[:-5].replace('/', '.') for f in files if os.path.exists('.lake/build/lib/lean/' + f[:-5] + '.olean')]
    print(f'{len(files)} modules, {len(built)} built, {len(files) - len(built)} without artifacts (skipped)', flush=True)
    for f in glob.glob(DUMP + '/*'): os.remove(f)
    open(DUMP + '/root.list', 'w').write('SerrePositivity\n')
    lock = ['zsh', 'scripts/refactor/with_build_lock.sh', '--class', 'coord', '--wait', '7200', '--']
    run(lock + ['lake', 'env', 'lean', '--run', 'research/cleanup-zero-base/dump_all.lean', DUMP + '/root.list', DUMP + '/root', 'ALL'])
    done = {l.split('\t')[0] for l in open(DUMP + '/root.modules.tsv', encoding='utf-8')}
    rest = collections.defaultdict(list)
    for m in built:
        if m not in done: rest['.'.join(m.split('.')[1:3])].append(m)
    chunks = []; cur = []
    for k, v in sorted(rest.items(), key=lambda kv: -len(kv[1])):
        if len(cur) + len(v) > 1500 and cur: chunks.append(cur); cur = []
        cur += v
    if cur: chunks.append(cur)
    for i, ch in enumerate(chunks):
        open(f'{DUMP}/chunk{i}.list', 'w').write('\n'.join(ch) + '\n')
        run(lock + ['lake', 'env', 'lean', '--run', 'research/cleanup-zero-base/dump_all.lean', f'{DUMP}/chunk{i}.list', f'{DUMP}/chunk{i}', f'{DUMP}/chunk{i}.list'])
    n = sum(1 for f in glob.glob(DUMP + '/*.decls.tsv') for _ in open(f, encoding='utf-8'))
    print('constants dumped', n, flush=True)
    if n < 300000: sys.exit('採取が途中で止まっている疑い（定数が 30 万未満）。dump/ の出力を確かめること')
W, X, TREE = WORK + '/W.pkl', WORK + '/X.pkl', WORK + '/tree.pkl'
if not SKIP or not os.path.exists(W):
    run([sys.executable, 'research/cleanup-zero-base/whole.py', DUMP, W])
    N = pickle.load(open(W, 'rb'))['N']; xn = {}; XD = {}
    for f in glob.glob(DUMP + '/*.xnames.tsv'):
        for l in open(f, encoding='utf-8'):
            a = l.rstrip('\n').split('\t'); xn[a[0]] = a[1]
    for f in glob.glob(DUMP + '/*.xdeps.tsv'):
        for l in open(f, encoding='utf-8'):
            a = l.rstrip('\n').split('\t')
            if a[0] in N and a[0] not in XD: XD[a[0]] = tuple(a[1].split()) if len(a) > 1 and a[1] else ()
    pickle.dump((xn, XD), open(X, 'wb'))
out = run([sys.executable, os.path.join(HERE, 'assign6.py'), W, X, '-', WORK + '/tree', TREE], capture_output=True, text=True).stdout
print(out)
run([sys.executable, os.path.join(HERE, 'page.py'), WORK + '/tree-sub.csv', WORK + '/tree.html', LABEL])
# 報告
T = pickle.load(open(TREE, 'rb')); N = pickle.load(open(W, 'rb'))['N']
rep = [f'概念の木 {LABEL}', '', out.strip(), '']
miss = [l.strip() for l in open(WORK + '/tree-missing-definitions.txt', encoding='utf-8') if l.strip()] if os.path.exists(WORK + '/tree-missing-definitions.txt') else []
rep.append(f'definitions.csv にあってコードから消えた定義：{len(miss)}（一覧は tree-missing-definitions.txt。改名なら definitions.csv の名前を直す）')
strip = lambda n: re.sub(r'^_private\..*?\.0\.', '', n)
if PREV and os.path.exists(PREV + '/tree.pkl'):
    P = pickle.load(open(PREV + '/tree.pkl', 'rb')); PN = pickle.load(open(PREV + '/W.pkl', 'rb'))['N']
    old = {strip(PN[x]['name']): c for x, c in P['con'].items()}; new = {strip(N[x]['name']): c for x, c in T['con'].items()}
    gone = set(old) - set(new); came = set(new) - set(old); moved = [n for n in set(old) & set(new) if old[n] != new[n]]
    rep += ['', f'前回（{PREV}）との差：宣言 {len(old)} → {len(new)}、消えた {len(gone)}、増えた {len(came)}、概念が変わった {len(moved)}']
    bc = collections.Counter();
    for n in gone: bc[('消えた', old[n])] += 1
    for n in came: bc[('増えた', new[n])] += 1
    for (k, c), v in sorted(bc.items(), key=lambda kv: -kv[1])[:30]: rep.append(f'  {k} {v}：{c}')
    mv = collections.Counter((old[n], new[n]) for n in moved)
    for (a, b), v in mv.most_common(20): rep.append(f'  概念が変わった {v}：{a} → {b}')
    with open(WORK + '/diff.csv', 'w', encoding='utf-8') as f:
        w = csv.writer(f); w.writerow(['declaration', 'change', 'old_concept', 'new_concept'])
        for n in sorted(gone): w.writerow([n, '消えた', old[n], ''])
        for n in sorted(came): w.writerow([n, '増えた', '', new[n]])
        for n in sorted(moved): w.writerow([n, '概念が変わった', old[n], new[n]])
open(WORK + '/report.txt', 'w', encoding='utf-8').write('\n'.join(rep) + '\n'); print('\n'.join(rep[-12:]))
