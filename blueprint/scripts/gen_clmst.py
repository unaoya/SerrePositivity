"""CLMST の章を Verso Blueprint の章モジュールとして生成する（2026-11-17）。gen_paper.py と同じ作り。
正本は research/clmst-coverage/（items.csv の種類・見出し、review/ch<N>.csv の状態・宣言・理由、edges.csv の引用の辺、toc.md の見出し）。
通常の CLMST 生成は scripts/audit2/coverage_blueprint.py が gen_cited.py に渡す。
- 各項目は一つのノード。ラベルは clmst_<番号>（式は clmst_eq_…）。
- 論文の中の辺（edges.csv の internal）は (uses := …) に。外の文献への辺（external）は本文に文献と番号を並べる。
- Lean の宣言に結ぶのは状態が own のものだけ（interface・partial は本文に宣言名と状態を書く。結ぶと形式化済みに数えられるため）。"""
import csv, re, sys, os, collections, json
sys.path.insert(0, os.path.dirname(__file__))
from common import Resolver, esc
res = Resolver()
P = 'research/clmst-coverage'; OUT = 'blueprint/SerreBlueprint/CLMST'
os.makedirs(OUT, exist_ok=True)
items = list(csv.DictReader(open(f'{P}/items.csv', encoding='utf-8')))
rev = {}
for ch in range(1, 9):
    for r in csv.DictReader(open(f'{P}/review/ch{ch}.csv', encoding='utf-8')): rev[r['number']] = r
edges = list(csv.DictReader(open(f'{P}/edges.csv', encoding='utf-8')))
heads = {}
for l in open(f'{P}/toc.md', encoding='utf-8'):
    m = re.match(r'\|\s*([0-9]+(?:\.[0-9]+)?)\s*\|\s*([^|]+?)\s*\|\s*([0-9]+)\s*\|', l)
    if m: heads.setdefault(m.group(1), m.group(2))
def label(n):
    if n.startswith('('): return 'clmst_eq_' + re.sub(r'[^0-9A-Za-z]+', '_', n.strip('()')).strip('_')
    return 'clmst_' + re.sub(r'[^0-9A-Za-z]+', '_', n).strip('_')
known = {r['number'] for r in items}
uses = collections.defaultdict(list); ext = collections.defaultdict(list)
for e in edges:
    if e['kind'] == 'internal' and e['depends_on'] in known and e['depends_on'] != e['number']:
        if label(e['depends_on']) not in uses[e['number']]: uses[e['number']].append(label(e['depends_on']))
    elif e['kind'] == 'external':
        if e['depends_on'] not in ext[e['number']]: ext[e['number']].append(e['depends_on'])
KIND = {'Theorem': 'theorem', 'Lemma': 'lemma_', 'Proposition': 'proposition', 'Corollary': 'corollary', 'Remark': 'proposition', 'Equation': 'definition', 'Figure': 'definition', 'Definition': 'definition'}
KINDJA = {'Theorem': '定理', 'Lemma': '補題', 'Proposition': '命題', 'Corollary': '系', 'Remark': '注意', 'Equation': '式', 'Figure': '図', 'Definition': '定義'}
STATUS = {'own': '本体にある', 'mathlib': 'Mathlib にある', 'both': '本体と Mathlib にある', 'partial': '一部', 'interface': '未証明の入力に依存', 'none': 'なし'}
by_sec = collections.defaultdict(list)
for r in items: by_sec[r['section'].split('.')[0]].append(r)
stats = collections.Counter(); modules = []
for sec in sorted(by_sec, key=int):
    imports = set(); body = []
    subs = collections.defaultdict(list)
    for r in by_sec[sec]: subs[r['section']].append(r)
    for sub in sorted(subs, key=lambda s: [int(x) for x in s.split('.')]):
        if sub != sec:
            body.append(f'# §{sub} {esc(heads.get(sub, ""))}\n')
            body.append('%%%\nnumber := false\ntag := "clmst-' + sub.replace('.', '-') + '"\n%%%\n')
        for r in subs[sub]:
            n = r['number']; rv = rev.get(n, {}); st = rv.get('status', '')
            linked = res.links(label(n), rv.get('declarations', ''), imports, st == 'own')
            stats['linked' if linked else 'nolink-' + (st or '?')] += 1
            opts = ''
            if linked: opts += f' (lean := "{", ".join(linked)}")'
            if uses[n]: opts += f' (uses := "{", ".join(uses[n])}")'
            title = r['title']
            body.append(f':::{KIND.get(r["kind"], "proposition")} "{label(n)}"{opts}')
            body.append(f'**{KINDJA.get(r["kind"], r["kind"])} {esc(n)}**　{esc(title)}。対応表の状態：{STATUS.get(st, st)}。\n')
            if rv.get('reason'): body.append(esc(rv['reason']) + '\n')
            decls = [x.split(' @ ', 1)[0].strip() for x in rv.get('declarations', '').split(' | ') if x.strip()]
            if decls and not linked:
                body.append('宣言：' + '、'.join('`' + d.replace('`', '') + '`' for d in decls) + '\n')
            if ext[n]:
                body.append('外の文献：' + '、'.join(esc(x) for x in ext[n]) + '\n')
            body.append(':::\n')
    mod = f'Section{sec}'
    hdr = ['import Verso', 'import VersoManual', 'import VersoBlueprint'] + [f'import {m}' for m in sorted(imports)] + \
          ['', 'open Verso.Genre', 'open Verso.Genre.Manual', 'open Informal', '',
           f'#doc (Manual) "§{sec} {heads.get(sec, "")}" =>', '%%%', 'number := false', f'tag := "clmst-{sec}"', '%%%', '',
           f'CLMST（Cai–Lee–Ma–Schwede–Tucker, arXiv 2209.04046v4）§{sec} の項目と、本体の宣言との対応。本文は対応表（`research/clmst-coverage`）の照合の理由で、論文の本文の写しではない。\n']
    res.write(f'{OUT}/{mod}.lean', '\n'.join(hdr + body) + '\n')
    modules.append(mod)
json.dump({'modules': modules, 'stats': dict(stats)}, open(f'{OUT}/clmst-generated.json', 'w'), ensure_ascii=False, indent=1)
print(modules, dict(stats))
