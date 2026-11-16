"""対応表の「名前 @ パス:行」を、今のソースから引き直す（2026-11-16）。改名表を順にたどる代わりに、
SerrePositivity と Mathlib のソースを名前空間つきで走査し、宣言の完全な名前から今のパスと行を決める。
名前は書かれた形（完全な名前、または名前空間の一部を省いた形）を、完全な名前の末尾に「.」の境目で合わせる。
候補が一つなら解決。複数なら元のパスと同じファイル名のものを選ぶ。それでも決まらないものと、見つからないものは未解決として残す（表は変えない）。
使い方：python3 refresh_by_source.py <csv> [<csv> ...] --cols <列名,...> --out <json> [--write]"""
import csv, io, json, os, re, sys, glob, collections
args = sys.argv[1:]
write = '--write' in args
out = args[args.index('--out') + 1]
cols = args[args.index('--cols') + 1].split(',')
files = [a for a in args if a.endswith('.csv') and a != out]
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|public|scoped|local|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+([^\s:({\[]+)')
NS = re.compile(r'^\s*namespace\s+(\S+)')
SEC = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|public\s+)*section(?:\s+(\S+))?\s*$')
END = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')
index = collections.defaultdict(list)   # full name -> [(path, line)]
def scan(path, rel):
    stack = []  # list of (kind, name parts)
    try:
        lines = open(path, encoding='utf-8', errors='ignore').read().split('\n')
    except OSError:
        return
    for i, l in enumerate(lines, 1):
        m = NS.match(l)
        if m:
            stack.append(('ns', m.group(1).split('.'))); continue
        m = SEC.match(l)
        if m:
            stack.append(('sec', [])); continue
        m = END.match(l)
        if m and stack:
            stack.pop(); continue
        m = DECL.match(l)
        if m:
            nm = m.group(2)
            if nm.startswith('_root_.'):
                full = nm[len('_root_.'):]
            else:
                prefix = [p for k, ps in stack for p in ps]
                full = '.'.join(prefix + [nm])
            index[full].append((rel, i))
for p in glob.glob('SerrePositivity/**/*.lean', recursive=True):
    scan(p, p)
ml = '.lake/packages/mathlib'
for p in glob.glob(ml + '/Mathlib/**/*.lean', recursive=True):
    scan(p, p[len(ml) + 1:])
# 改名表を順に（KL-W1 → B3 → B3′）。古い名前から今の名前へ
renames = {}
def chain(rows):
    for r in rows:
        if r.get('old') and r.get('new') and r['old'] != r['new']:
            renames[r['old']] = r['new']
for path, loader in [('scripts/refactor/targets/kl-namespace-map.json', lambda d: d['rows']),
                     ('formalization-plans/stage-ii/bulk-b3prime/B4/namespace-rewrite-map.json', lambda d: d['rows'])]:
    if os.path.exists(path):
        chain(loader(json.load(open(path))))
import gzip
b3 = 'formalization-plans/stage-ii/bulk-w1-b3/declaration-names.jsonl.gz'
if os.path.exists(b3):
    chain(json.loads(l) for l in gzip.open(b3, 'rt'))
def renamed(n):
    seen = set()
    while n in renames and n not in seen:
        seen.add(n); n = renames[n]
    return n
by_short = collections.defaultdict(list)
for full in index:
    by_short[full.split('.')[-1]].append(full)
by_suffix = collections.defaultdict(list)
for full in index:
    parts = full.split('.')
    for k in range(len(parts)):
        by_suffix['.'.join(parts[k:])].append(full)
stats = collections.Counter(); unresolved = []; changed = []
def fix(entry, src):
    if ' @ ' not in entry:
        return entry
    name, loc = entry.split(' @ ', 1); name = name.strip(); loc = loc.strip()
    path, _, line = loc.rpartition(':')
    if not path:
        path, line = loc, ''
    if not (path.startswith('SerrePositivity/') or path.startswith('Mathlib/')):
        stats['skip'] += 1; return entry
    key = name.split(' ')[0].split('（')[0].strip()
    how = 'name'
    cands = sorted(set(by_suffix.get(key, [])))
    if not cands:
        rk = renamed(key)
        if rk != key:
            cands = sorted(set(by_suffix.get(rk, []))); how = 'rename'
    if not cands and path.startswith('SerrePositivity/'):
        # 名前空間が変わった本体の宣言だけ、末尾の成分で探す（Mathlib の構造体の構成子・フィールドは走査で拾えないので使わない）
        cands = sorted(set(by_short.get(key.split('.')[-1], []))); how = 'short'
    locs = [(f, pl) for f in cands for pl in index[f]]
    if len(locs) > 1 and how != 'short':
        same = [x for x in locs if x[1][0] == path]
        base = os.path.basename(path)
        if not same:
            same = [x for x in locs if os.path.basename(x[1][0]) == base]
        if len(same) >= 1:
            locs = same[:1]
    if len(locs) > 1 and how == 'short':
        tail = key.split('.')
        def score(x):
            fp = x[0].split('.'); k = 0
            while k < min(len(fp), len(tail)) and fp[-1-k] == tail[-1-k]: k += 1
            return k
        best = max(score(x) for x in locs)
        top = [x for x in locs if score(x) == best]
        locs = top if len(top) == 1 else top
    if how == 'short' and locs:
        tail = key.split('.')
        need = min(2, len(tail))
        def score2(x):
            fp = x[0].split('.'); k = 0
            while k < min(len(fp), len(tail)) and fp[-1-k] == tail[-1-k]: k += 1
            return k
        locs = [x for x in locs if score2(x) >= need]
        if len(locs) > 1:
            same = [x for x in locs if os.path.basename(x[1][0]) == os.path.basename(path)]
            locs = same if len(same) == 1 else locs
    if not locs and os.path.exists(path if path.startswith('SerrePositivity/') else os.path.join(ml, path)):
        stats['kept:unverified'] += 1; return entry
    if len(locs) > 1 and os.path.exists(path if path.startswith('SerrePositivity/') else os.path.join(ml, path)):
        stats['kept:ambiguous-field'] += 1; return entry
    if len(locs) != 1:
        stats['unresolved:none' if not locs else 'unresolved:ambiguous'] += 1
        unresolved.append({'source': src, 'entry': entry, 'candidates': [f'{f} @ {p}:{n}' for f, (p, n) in locs[:6]]})
        return entry
    full, (np_, nl) = locs[0]
    shown = name if how == 'name' else full + name[len(key):]
    new = f'{shown} @ {np_}:{nl}'
    if new == entry:
        stats['same'] += 1
    else:
        stats[('moved' if np_ != path else 'line') + ':' + how] += 1
        changed.append({'source': src, 'old': entry, 'new': new})
    return new
for f in files:
    raw = open(f, newline='', encoding='utf-8').read(); nl = '\r\n' if '\r\n' in raw else '\n'
    rows = list(csv.DictReader(io.StringIO(raw)))
    if not rows:
        continue
    fields = list(rows[0].keys()); ch = 0
    for r in rows:
        for c in cols:
            if c not in r or not r[c]:
                continue
            parts = r[c].split(' | ')
            new = [fix(p, f'{f}:{r.get("number", "")}') for p in parts]
            if new != parts:
                r[c] = ' | '.join(new); ch += 1
    if write and ch:
        o = io.StringIO(); w = csv.DictWriter(o, fields, lineterminator=nl); w.writeheader(); w.writerows(rows)
        open(f, 'w', newline='', encoding='utf-8').write(o.getvalue())
json.dump({'stats': dict(stats), 'unresolved': unresolved, 'changed': changed}, open(out, 'w'), ensure_ascii=False, indent=1)
print(dict(stats))
