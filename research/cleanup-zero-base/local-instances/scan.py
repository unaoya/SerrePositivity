#!/usr/bin/env python3
"""局所 instance の置き直しの内訳（ソースを読む）。
  python3 research/cleanup-zero-base/local-instances/scan.py <出力 csv>
`local instance …` と `attribute [local instance] …` を全部拾い、型（何の構造を何に）と右辺（何を置いているか）で分ける。"""
import sys, re, subprocess, csv, collections
OUT = sys.argv[1]
files = [f for f in subprocess.run(['git', 'ls-files', 'SerrePositivity'], capture_output=True, text=True).stdout.split() if f.endswith('.lean') and '/Archive/' not in f]
def norm(s):
    s = re.sub(r'\.\{[^}]*\}', '', s); s = re.sub(r'\b_root_\.', '', s); s = re.sub(r'\bSerrePositivity\.', '', s)
    return ' '.join(s.split())
rows = []; attr = collections.Counter()
for f in files:
    L = open(f, encoding='utf-8').read().split('\n')
    for i, l in enumerate(L):
        m = re.match(r'\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?local instance\b(.*)', l)
        if m:
            t = m.group(1); j = i
            while not re.search(r':=|\bwhere\b', t) and j < i + 12 and j + 1 < len(L): j += 1; t += ' ' + L[j]
            head, _, rhs = re.split(r'(:=|\bwhere\b)', t, maxsplit=1) if re.search(r':=|\bwhere\b', t) else (t, '', '')
            sep = _; 
            if not rhs.strip() and sep == ':=' and j + 1 < len(L): rhs = L[j + 1]
            depth = 0; last = -1
            for k, ch in enumerate(head):
                if ch in '([{⦃': depth += 1
                elif ch in ')]}⦄': depth -= 1
                elif ch == ':' and depth == 0: last = k
            typ = norm(head[last + 1:]) if last >= 0 else norm(head)
            name = norm(head[:last]).split(' ')[0] if last >= 0 else ''
            binders = bool(re.search(r'[\(\[\{]', head[:last])) if last >= 0 else False
            cls = re.match(r'@?([\w.]+)', typ); cls = cls.group(1) if cls else ''
            body = 'where（その場で構成）' if sep == 'where' else norm(rhs)[:160]
            rows.append({'file': f, 'line': i + 1, 'name': name if not name.startswith(('(', '[', '{', ':')) else '', 'class': cls, 'type': typ[:220], 'has_binders': 'yes' if binders else '', 'rhs': body,
                         'area': '/'.join(f.split('/')[1:3])})
        m = re.match(r'\s*attribute\s*\[([^\]]*\blocal instance\b[^\]]*)\]\s*(.*)', l)
        if m:
            for n in m.group(2).split():
                if n == 'in': break
                attr[(n, '/'.join(f.split('/')[1:3]))] += 1
with open(OUT, 'w', encoding='utf-8', newline='') as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
with open(OUT.replace('.csv', '-attribute.csv'), 'w', encoding='utf-8', newline='') as f:
    w = csv.writer(f); w.writerow(['declaration', 'area', 'count'])
    for (n, a), c in sorted(attr.items(), key=lambda kv: -kv[1]): w.writerow([n, a, c])
print('local instance', len(rows), 'files', len({r['file'] for r in rows}), '| attribute [local instance]', sum(attr.values()), 'distinct', len({n for n, _ in attr}))
C = collections.Counter(r['class'] for r in rows)
print('by class:'); [print(' ', c, k) for k, c in C.most_common(40)]
T = collections.defaultdict(list)
for r in rows: T[r['type']].append(r)
print('distinct types', len(T), '| types declared once', sum(len(v) == 1 for v in T.values()))
print('top types:')
for t, v in sorted(T.items(), key=lambda kv: -len(kv[1]))[:30]:
    rh = collections.Counter(x['rhs'] for x in v)
    print(' ', len(v), '|', t[:100], '| 右辺の種類', len(rh), '| 最多', rh.most_common(1)[0][0][:60], rh.most_common(1)[0][1])
print('where bodies', sum(r['rhs'].startswith('where') for r in rows), 'with binders', sum(r['has_binders'] == 'yes' for r in rows))
print('by area:'); [print(' ', c, k) for k, c in collections.Counter(r['area'] for r in rows).most_common(20)]
