"""整理の進み具合を数える（字面、Lean なし）。指定したコミットの SerrePositivity/（Archive を除く）について、
ファイル数・行数・文字数・宣言数などを数え、research/cleanup-metrics/history.csv に一行足し、
ディレクトリごとの内訳を research/cleanup-metrics/by-dir/<コミット>.csv に書く。
使い方（root で）：python3 scripts/coord/metrics.py [コミット（既定 HEAD）] [ラベル]
- 宣言は行頭のキーワードで数える（自動生成は入らない。カーネルの宣言数とは違う）。
- 文字数は改行を含む Unicode の符号位置の数。同じコミットを二度数えたら、行を置き換える。"""
import subprocess, re, collections, csv, os, sys
commit = subprocess.run(['git', 'rev-parse', sys.argv[1] if len(sys.argv) > 1 else 'HEAD'], capture_output=True, text=True).stdout.strip()
label = sys.argv[2] if len(sys.argv) > 2 else ''
date = subprocess.run(['git', 'show', '-s', '--format=%cI', commit], capture_output=True, text=True).stdout.strip()[:16]
paths = [p for p in subprocess.run(['git', 'ls-tree', '-r', '--name-only', commit, 'SerrePositivity'], capture_output=True, text=True).stdout.split('\n')
         if p.endswith('.lean') and not p.startswith('SerrePositivity/Archive/')]
proc = subprocess.Popen(['git', 'cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
def blob(p):
    proc.stdin.write(f'{commit}:{p}\n'.encode()); proc.stdin.flush()
    size = int(proc.stdout.readline().split()[2]); data = proc.stdout.read(size); proc.stdout.read(1)
    return data.decode('utf-8', errors='ignore')
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|public|scoped|local|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque)\b')
ALIAS = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:\w+\s+)*(deprecated_alias\w*|alias)\b|@\[deprecated')
KIND = {'theorem': 'thm', 'lemma': 'thm', 'def': 'def', 'abbrev': 'def', 'opaque': 'def', 'instance': 'inst', 'structure': 'struct', 'class': 'struct', 'inductive': 'struct'}
COLS = ['files', 'lines', 'chars', 'code', 'decls', 'thm', 'def', 'inst', 'struct', 'private', 'alias', 'doc', 'moddoc', 'comment', 'blank', 'import', 'scaffold', 'setopt', 'over100', 'files_le3']
def area(p):
    q = p.split('/')
    return '/'.join(q[1:3]) if len(q) > 3 else (q[1] if len(q) > 2 else '(root)')
tot = collections.Counter(); bydir = collections.defaultdict(collections.Counter)
for p in paths:
    text = blob(p); c = collections.Counter(); c['chars'] = len(text)
    L = text.split('\n')
    if L and L[-1] == '': L = L[:-1]
    state = None
    for l in L:
        s = l.strip()
        if len(l) > 100: c['over100'] += 1
        if state:
            c[state] += 1
            if '-/' in s: state = None
            continue
        if s.startswith('/-!'): c['moddoc'] += 1; state = None if '-/' in s[3:] else 'moddoc'; continue
        if s.startswith('/--'): c['doc'] += 1; state = None if '-/' in s[3:] else 'doc'; continue
        if s.startswith('/-'): c['comment'] += 1; state = None if '-/' in s[2:] else 'comment'; continue
        if s == '': c['blank'] += 1; continue
        if s.startswith('--'): c['comment'] += 1; continue
        if re.match(r'^(public |private |meta )*import ', s) or s == 'module': c['import'] += 1; continue
        m = DECL.match(l)
        if not m and re.match(r'^(set_option|open |namespace |end\b|section\b|noncomputable section|public section|universe |variable|local |attribute |@\[expose\] public section|suppress_compilation)', s):
            c['setopt' if s.startswith('set_option') else 'scaffold'] += 1; continue
        if ALIAS.search(l): c['alias'] += 1; continue
        if m:
            c['decls'] += 1; c[KIND[m.group(1)]] += 1
            if re.search(r'\bprivate\b', l[:m.start(1)]): c['private'] += 1
        c['code'] += 1
    c['lines'] = len(L); c['files'] = 1
    if c['decls'] <= 3: c['files_le3'] = 1
    tot.update(c); bydir[area(p)].update(c)
proc.stdin.close()
D = 'research/cleanup-metrics'; os.makedirs(f'{D}/by-dir', exist_ok=True)
H = f'{D}/history.csv'; rows = []
if os.path.exists(H): rows = [r for r in csv.DictReader(open(H, encoding='utf-8')) if r['commit'] != commit[:9]]
rows.append({'date': date, 'commit': commit[:9], 'label': label, **{k: tot[k] for k in COLS}})
rows.sort(key=lambda r: r['date'])
with open(H, 'w', encoding='utf-8', newline='') as f:
    w = csv.DictWriter(f, fieldnames=['date', 'commit', 'label'] + COLS); w.writeheader(); w.writerows(rows)
with open(f'{D}/by-dir/{commit[:9]}.csv', 'w', encoding='utf-8', newline='') as f:
    w = csv.DictWriter(f, fieldnames=['dir'] + COLS); w.writeheader()
    for k, v in sorted(bydir.items(), key=lambda x: -x[1]['lines']): w.writerow({'dir': k, **{c: v[c] for c in COLS}})
print(commit[:9], label, {k: tot[k] for k in COLS})
