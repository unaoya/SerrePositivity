"""引用文献の章を Verso Blueprint の章モジュールとして生成する（2026-11-18）。gen_paper.py と同じ作りを文献の表ごとに回す。
正本は research/<key>-coverage/（items.csv の種類・題、review/ch*.csv の状態・宣言・理由、edges.csv の引用の辺、toc.md の見出し）。
生成物を手で直さない。使い方（リポジトリの root で）：python3 blueprint/scripts/gen_cited.py clmst bs17 bm18 rydh bs
- 各項目は一つのノード。ラベルは <key>_<番号>（式は <key>_eq_…）。文献の中の辺（internal）は (uses := …) に、外の文献への辺は本文に並べる。
- Lean の宣言に結ぶのは状態が own・mathlib・both のものだけ（partial・interface は本文に宣言名と状態を書く）。"""
import csv, re, sys, os, glob, collections, json
sys.path.insert(0, os.path.dirname(__file__))
from common import Resolver, paths_of, esc
SOURCES = {
 'clmst': ('CLMST', 'CLMST（Cai–Lee–Ma–Schwede–Tucker, Perfectoid signature, perfectoid Hilbert–Kunz multiplicity, …, arXiv 2209.04046v4）'),
 'bs17': ('BS17', 'BS17（Bhatt–Scholze, Projectivity of the Witt vector affine Grassmannian, arXiv 1507.06490v3）'),
 'bm18': ('BM18', 'BM18（Bhatt–Mathew, The arc-topology, arXiv 1807.04725v4）'),
 'rydh': ('Rydh', 'Rydh（Submersions and effective descent of étale morphisms, arXiv 0710.2488v3）'),
 'bs': ('BS', 'BS（Bhatt–Scholze, Prisms and prismatic cohomology、著者版）'),
}
KIND = {'Theorem': 'theorem', 'Lemma': 'lemma_', 'Proposition': 'proposition', 'Corollary': 'corollary', 'Definition': 'definition',
        'Notation': 'definition', 'Construction': 'definition', 'Convention': 'definition', 'Equation': 'definition', 'Example': 'proposition',
        'Remark': 'proposition', 'Claim': 'lemma_', 'Conjecture': 'proposition', 'Question': 'proposition', 'Caution': 'proposition'}
KINDJA = {'Theorem': '定理', 'Lemma': '補題', 'Proposition': '命題', 'Corollary': '系', 'Remark': '注意', 'Equation': '式', 'Definition': '定義',
          'Example': '例', 'Notation': '記法', 'Construction': '構成', 'Convention': '規約', 'Claim': '主張', 'Conjecture': '予想', 'Question': '問い', 'Caution': '注意'}
STATUS = {'own': '本体にある', 'mathlib': 'Mathlib にある', 'both': '本体と Mathlib にある', 'partial': '一部', 'interface': '未証明の入力に依存', 'none': 'なし'}
def slug(s): return re.sub(r'[^0-9A-Za-z]+', '_', s).strip('_')
def skey(s): return [(0, int(x)) if x.isdigit() else (1, x) for x in re.split(r'[.]', s) if x != '']
def gen(key):
    dirname, title = SOURCES[key]
    P = f'research/{key}-coverage'; OUT = f'blueprint/SerreBlueprint/{dirname}'
    os.makedirs(OUT, exist_ok=True)
    for old in glob.glob(f'{OUT}/Section*.lean'): os.remove(old)
    items = list(csv.DictReader(open(f'{P}/items.csv', encoding='utf-8')))
    rev = {}
    for f in sorted(glob.glob(f'{P}/review/ch*.csv')):
        for r in csv.DictReader(open(f, encoding='utf-8')): rev[r['number']] = r
    edges = list(csv.DictReader(open(f'{P}/edges.csv', encoding='utf-8'))) if os.path.exists(f'{P}/edges.csv') else []
    heads = {}
    if os.path.exists(f'{P}/toc.md'):
        for l in open(f'{P}/toc.md', encoding='utf-8'):
            m = re.match(r'\|\s*([0-9A-Z]+(?:\.[0-9]+)*)\s*\|\s*([^|]+?)\s*\|', l)
            if m: heads.setdefault(m.group(1), m.group(2))
    def label(n):
        if n.startswith('('): return f'{key}_eq_' + slug(n.strip('()'))
        return f'{key}_' + slug(n)
    def section(r):
        s = r.get('section') or ''
        if s: return s
        n = r['number'].strip('()'); return n.split('.')[0]
    known = {r['number'] for r in items}
    uses = collections.defaultdict(list); ext = collections.defaultdict(list)
    for e in edges:
        if e['kind'] == 'internal' and e['depends_on'] in known and e['depends_on'] != e['number']:
            if label(e['depends_on']) not in uses[e['number']]: uses[e['number']].append(label(e['depends_on']))
        elif e['kind'] == 'external' and e['depends_on'] not in ext[e['number']]: ext[e['number']].append(e['depends_on'])
    res = Resolver(paths_of(r.get('declarations', '') for r in rev.values()))
    by_sec = collections.defaultdict(list)
    for r in items: by_sec[section(r).split('.')[0]].append(r)
    stats = collections.Counter(); modules = []; seen_labels = set()
    for sec in sorted(by_sec, key=skey):
        imports = set(); body = []
        subs = collections.defaultdict(list)
        for r in by_sec[sec]: subs[section(r)].append(r)
        for sub in sorted(subs, key=skey):
            if sub != sec:
                body.append(f'# §{sub} {esc(heads.get(sub, ""))}\n')
                body.append('%%%\nnumber := false\ntag := "' + f'{key}-' + slug(sub).replace('_', '-') + '"\n%%%\n')
            for r in subs[sub]:
                n = r['number']; rv = rev.get(n, {}); st = rv.get('status', '') or 'none'
                lab = label(n)
                if lab in seen_labels: continue
                seen_labels.add(lab)
                linked = []
                if st in ('own', 'mathlib', 'both'):
                    for e in [x.strip() for x in rv.get('declarations', '').split(' | ') if x.strip()]:
                        x = res.resolve(e)
                        if x: linked.append(x[0]); imports.add(x[1])
                stats[st] += 1; stats['linked' if linked else 'nolink'] += 1
                opts = ''
                if linked: opts += f' (lean := "{", ".join(linked)}")'
                if uses[n]: opts += f' (uses := "{", ".join(uses[n])}")'
                ttl = r.get('title_ja') or r.get('title') or ''
                ttl = re.sub(r'<[^>]+>', '', ttl)
                pk = rv.get('partial_kind', '')
                state = STATUS.get(st, st) + (f'（{pk}）' if st == 'partial' and pk else '')
                body.append(f':::{KIND.get(r["kind"], "proposition")} "{lab}"{opts}')
                body.append(f'*{KINDJA.get(r["kind"], esc(r["kind"]))} {esc(n)}*　{esc(ttl)}。対応表の状態：{state}。\n')
                if rv.get('reason'): body.append(esc(rv['reason']) + '\n')
                decls = [x.split(' @ ', 1)[0].strip() for x in rv.get('declarations', '').split(' | ') if x.strip()]
                if decls and not linked: body.append('宣言：' + '、'.join('`' + d.replace('`', '') + '`' for d in decls) + '\n')
                if ext[n]: body.append('外の文献：' + '、'.join(esc(x) for x in ext[n]) + '\n')
                body.append(':::\n')
        mod = f'Section{slug(sec)}'
        head = esc(heads.get(sec, ''))
        hdr = ['import Verso', 'import VersoManual', 'import VersoBlueprint'] + [f'import {m}' for m in sorted(imports)] + \
              ['', 'open Verso.Genre', 'open Verso.Genre.Manual', 'open Informal', '',
               f'#doc (Manual) "§{sec} {heads.get(sec, "")}" =>', '%%%', 'number := false', f'tag := "{key}-{slug(sec)}"', '%%%', '',
               f'{dirname} §{sec} の項目と、本体の宣言との対応。本文は対応表（`research/{key}-coverage`）の照合の理由で、原典の本文の写しではない。\n']
        open(f'{OUT}/{mod}.lean', 'w', encoding='utf-8').write('\n'.join(hdr + body) + '\n')
        modules.append(mod)
    json.dump({'key': key, 'dir': dirname, 'title': title, 'modules': modules, 'stats': dict(stats)},
              open(f'{OUT}/generated.json', 'w'), ensure_ascii=False, indent=1)
    print(key, len(modules), 'sections', dict(stats))
for k in sys.argv[1:]: gen(k)
